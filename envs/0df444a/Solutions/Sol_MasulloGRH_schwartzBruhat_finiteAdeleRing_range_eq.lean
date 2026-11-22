-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_finiteAdeleRing_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:58:47.858302+00:00
-- url     : https://prove2.me/submissions/76164858-871d-4b48-b961-2a6b843a7bad

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_LCAGroup_isCompact_annihilator_of_isOpen
import Theorems.Thm_LCAGroup_isCompact_iff_isOpen_annihilator
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_RiemannMasullo_isCompact_closure_restrictedProduct_iff

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_schwartzBruhat_finiteAdeleRing_range_eq

open MasulloGRH Topology Filter Set
open scoped RestrictedProduct

section Elem
variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- The subset `ℝ^m × 𝕋^n × {0} × {0}` of `ℝ^m × 𝕋^n × ℤ^r × F`. -/
def compSet (m n r s : ℕ) (d : Fin s → ℕ) : Set (Multiplicative (ElemGroup m n r s d)) :=
  {e | (Multiplicative.toAdd e).2.2 = 0}

theorem t1_elem : T1Space (Multiplicative (ElemGroup m n r s d)) :=
  inferInstanceAs (T1Space (ElemGroup m n r s d))

theorem isOpen_compSet : IsOpen (compSet m n r s d) := by
  have hc : Continuous fun e : Multiplicative (ElemGroup m n r s d) =>
      (Multiplicative.toAdd e).2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_toAdd)
  exact (isOpen_discrete ({0} : Set ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))))).preimage hc

theorem isPreconnected_compSet : IsPreconnected (compSet m n r s d) := by
  let φ : (Fin m → ℝ) × (Fin n → ℝ) → Multiplicative (ElemGroup m n r s d) :=
    fun p => Multiplicative.ofAdd (p.1, fun j => ((p.2 j : ℝ) : UnitAddCircle), 0, 0)
  have hφ : Continuous φ := by
    refine continuous_ofAdd.comp ?_
    refine continuous_fst.prodMk (Continuous.prodMk ?_ continuous_const)
    exact continuous_pi fun j =>
      (AddCircle.continuous_mk' (1 : ℝ)).comp ((continuous_apply j).comp continuous_snd)
  have hrange : Set.range φ = compSet m n r s d := by
    ext e
    constructor
    · rintro ⟨p, rfl⟩; rfl
    · intro he
      have ht : ∀ j, ∃ t : ℝ, ((t : ℝ) : UnitAddCircle) = (Multiplicative.toAdd e).2.1 j :=
        fun j => QuotientAddGroup.mk_surjective _
      choose t ht using ht
      refine ⟨((Multiplicative.toAdd e).1, t), ?_⟩
      show Multiplicative.ofAdd _ = e
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      have he' : (Multiplicative.toAdd e).2.2 = 0 := he
      ext1
      · rfl
      ext1
      · exact funext ht
      · exact he'.symm
  rw [← hrange]
  exact isPreconnected_range hφ

theorem exists_openSubgroup_ker {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H]
    (π : H →* Multiplicative (ElemGroup m n r s d)) (hc : Continuous π) (ho : IsOpenMap π) :
    ∃ V : Subgroup H, IsOpen (V : Set H) ∧ ∀ x ∈ V, π x = 1 := by
  have := t1_elem (m := m) (n := n) (r := r) (s := s) (d := d)
  have h1O : (1 : Multiplicative (ElemGroup m n r s d)) ∈ compSet m n r s d := rfl
  have key : ∀ W : Set (Multiplicative (ElemGroup m n r s d)), IsOpen W → 1 ∈ W →
      ∃ V : Subgroup H, IsOpen (V : Set H) ∧ (∀ x ∈ V, π x ∈ W ∩ compSet m n r s d) ∧
        compSet m n r s d ⊆ π '' V := by
    intro W hW h1W
    have hU : IsOpen (π ⁻¹' (W ∩ compSet m n r s d)) := (hW.inter isOpen_compSet).preimage hc
    have h1U : (1 : H) ∈ π ⁻¹' (W ∩ compSet m n r s d) := by
      simp only [Set.mem_preimage, map_one]; exact ⟨h1W, h1O⟩
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1U
    refine ⟨V.toOpenSubgroup.toSubgroup, V.toOpenSubgroup.isOpen, fun x hx => hV hx, ?_⟩
    let P := V.toOpenSubgroup.toSubgroup.map π
    have hPo : IsOpen (P : Set (Multiplicative (ElemGroup m n r s d))) := by
      rw [Subgroup.coe_map]; exact ho _ V.toOpenSubgroup.isOpen
    have hPc : IsClosed (P : Set (Multiplicative (ElemGroup m n r s d))) := Subgroup.isClosed_of_isOpen P hPo
    have := isPreconnected_compSet.subset_isClopen ⟨hPc, hPo⟩ ⟨1, h1O, P.one_mem⟩
    rwa [Subgroup.coe_map] at this
  have hsub : compSet m n r s d ⊆ {1} := by
    intro e he
    by_contra hne
    obtain ⟨V, -, hV, hO⟩ := key {e}ᶜ isOpen_compl_singleton (fun h => hne h.symm)
    obtain ⟨x, hx, rfl⟩ := hO he
    exact (hV x hx).1 rfl
  obtain ⟨V, hVo, hV, -⟩ := key univ isOpen_univ (mem_univ _)
  exact ⟨V, hVo, fun x hx => hsub (hV x hx).2⟩

theorem elem_dims_zero (hfin : Finite (ElemGroup m n r s d)) : m = 0 ∧ n = 0 ∧ r = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hm
    have i0 : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    have : Finite ℝ := Finite.of_injective
      (fun t : ℝ => ((fun _ => t, 0, 0, 0) : ElemGroup m n r s d))
      (fun t t' htt => by simpa using congrArg (fun e : ElemGroup m n r s d => e.1 i0) htt)
    exact not_finite ℝ
  · by_contra hn
    have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have : Infinite (Set.Ico (0 : ℝ) (0 + 1)) :=
      (Set.Ico_infinite (by norm_num : (0 : ℝ) < 0 + 1)).to_subtype
    have : Infinite UnitAddCircle :=
      Infinite.of_injective (AddCircle.equivIco (1 : ℝ) 0).symm (Equiv.injective _)
    have : Finite UnitAddCircle := Finite.of_injective
      (fun t : UnitAddCircle => ((0, fun _ => t, 0, 0) : ElemGroup m n r s d))
      (fun t t' htt => by simpa using congrArg (fun e : ElemGroup m n r s d => e.2.1 i0) htt)
    exact not_finite UnitAddCircle
  · by_contra hr
    have i0 : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have : Finite ℤ := Finite.of_injective
      (fun t : ℤ => ((0, 0, fun _ => t, 0) : ElemGroup m n r s d))
      (fun t t' htt => by simpa using congrArg (fun e : ElemGroup m n r s d => e.2.2.1 i0) htt)
    exact not_finite ℤ

theorem rapidDecay_of_finite [Finite (ElemGroup 0 0 0 s d)] (g : ElemGroup 0 0 0 s d → ℂ) :
    IsRapidDecay g := by
  obtain ⟨M, hM⟩ := (Set.finite_range fun e => ‖g e‖).bddAbove
  have hM' : ∀ e, ‖g e‖ ≤ M := fun e => hM ⟨e, rfl⟩
  have hconst : ∀ a b, elemLift g a b = fun _ => elemLift g a b 0 := fun a b =>
    funext fun xt => congrArg (elemLift g a b) (Subsingleton.elim xt 0)
  refine ⟨fun a b => ?_, fun i j k => ⟨max M 0, fun a b xt => ?_⟩⟩
  · rw [hconst a b]; exact contDiff_const
  · have ha : ‖a‖ = 0 := by rw [Subsingleton.elim a 0, norm_zero]
    have hx : ‖xt.1‖ = 0 := by rw [Subsingleton.elim xt.1 0, norm_zero]
    have hD : ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖ ≤ max M 0 := by
      rw [hconst a b]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [norm_iteratedFDeriv_zero]; exact (hM' _).trans (le_max_left _ _)
      · rw [iteratedFDeriv_const_of_ne hk.ne', Pi.zero_apply, norm_zero]; exact le_max_right _ _
    have h1 : ‖a‖ ^ j ≤ 1 := by rw [ha]; exact pow_le_one₀ le_rfl zero_le_one
    have h2 : ‖xt.1‖ ^ i ≤ 1 := by rw [hx]; exact pow_le_one₀ le_rfl zero_le_one
    calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖
        ≤ 1 * 1 * max M 0 := by gcongr
      _ = max M 0 := by ring

end Elem


section Generic

theorem isLocallyConstant_of_openSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {f : G → ℂ} (K : Subgroup G) (hK : IsOpen (K : Set G))
    (hf : ∀ x, ∀ y ∈ K, f (x * y) = f x) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_exists_open f).2 fun x => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' K, hK.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · show x⁻¹ * x ∈ K
    rw [inv_mul_cancel]; exact K.one_mem
  · intro y hy
    have := hf x (x⁻¹ * y) hy
    rwa [mul_inv_cancel_left] at this

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

theorem isCompact_of_structural
    (hb : ∀ C : Set G, IsCompact C → ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsCompact (H : Set G) ∧ C ⊆ H)
    {Γ k : Subgroup G} (hs : IsStructuralPair Γ k) : IsCompact (Γ : Set G) := by
  obtain ⟨U, hUc, -, -, hUgen⟩ := hs.2.1
  obtain ⟨H, -, hHc, hUH⟩ := hb U hUc
  have hΓH : Γ ≤ H := hUgen ▸ (Subgroup.closure_le H).2 hUH
  exact hHc.of_isClosed_subset (Subgroup.isClosed_of_isOpen Γ hs.1) hΓH

theorem gen_mem
    (hb : ∀ C : Set G, IsCompact C → ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsCompact (H : Set G) ∧ C ⊆ H)
    {Γ k : Subgroup G} {m n r s : ℕ} {d : Fin s → ℕ}
    (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (g : ElemGroup m n r s d → ℂ) :
    IsLocallyConstant (extendPullback Γ π g) ∧ HasCompactSupport (extendPullback Γ π g) := by
  classical
  have hΓc := isCompact_of_structural hb hs
  have hΓo : IsOpen (Γ : Set G) := hs.1
  have : CompactSpace Γ := isCompact_iff_compactSpace.mp hΓc
  obtain ⟨V, hVo, hV⟩ := exists_openSubgroup_ker π hπ.2.1 hπ.2.2.1
  let K : Subgroup G := V.map Γ.subtype
  have hKo : IsOpen (K : Set G) := by
    rw [Subgroup.coe_map]; exact hΓo.isOpenMap_subtype_val _ hVo
  refine ⟨isLocallyConstant_of_openSubgroup K hKo ?_, ?_⟩
  · rintro x _ ⟨v, hv, rfl⟩
    have hv' : Γ.subtype v = (v : G) := rfl
    rw [hv']
    by_cases hx : x ∈ Γ
    · have hxy : x * (v : G) ∈ Γ := Γ.mul_mem hx v.2
      unfold extendPullback
      rw [dif_pos hx, dif_pos hxy]
      have : (⟨x * (v : G), hxy⟩ : Γ) = ⟨x, hx⟩ * v := rfl
      rw [this, map_mul, hV v hv, mul_one]
    · have hxy : x * (v : G) ∉ Γ := fun h => hx (by simpa using Γ.mul_mem h (Γ.inv_mem v.2))
      unfold extendPullback
      rw [dif_neg hx, dif_neg hxy]
  · refine HasCompactSupport.intro hΓc fun x hx => ?_
    unfold extendPullback
    rw [dif_neg (show x ∉ Γ from hx)]

theorem range_sub
    (hb : ∀ C : Set G, IsCompact C → ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsCompact (H : Set G) ∧ C ⊆ H)
    (f : SchwartzBruhat G) :
    IsLocallyConstant (f : G → ℂ) ∧ HasCompactSupport (f : G → ℂ) := by
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {h | IsLocallyConstant h ∧ HasCompactSupport h}
      zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
      add_mem' := fun hf hh => ⟨hf.1.comp₂ hh.1 (· + ·), hf.2.add hh.2⟩
      smul_mem' := fun c _ hf => ⟨hf.1.comp (c • ·), hf.2.smul_left (f := fun _ => c)⟩ }
  have hle : schwartzBruhatSubmodule G ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩
    exact gen_mem hb π hs hπ g.toFun
  exact hle f.2

theorem mem_of_lc
    (hb : ∀ C : Set G, IsCompact C → ∃ H : Subgroup G, IsOpen (H : Set G) ∧ IsCompact (H : Set G) ∧ C ⊆ H)
    {h : G → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    h ∈ schwartzBruhatSubmodule G := by
  classical
  obtain ⟨Γ, hΓo, hΓc, hsupp⟩ := hb _ hcs
  have hO : IsOpen {p : G × G | h (p.1 * p.2) = h p.1} := by
    have := ((hlc.comp_continuous continuous_mul).comp₂ (hlc.comp_continuous continuous_fst)
      (· = ·)) {True}
    convert this using 1
    ext p; simp
  obtain ⟨u, v, -, hvo, hΓu, h1v, huv⟩ := generalized_tube_lemma hΓc isCompact_singleton hO
    (by
      intro p hp
      obtain ⟨-, hp2⟩ := hp
      rw [Set.mem_singleton_iff] at hp2
      show h (p.1 * p.2) = h p.1
      rw [hp2, mul_one])
  have hinv : ∀ x ∈ Γ, ∀ y ∈ v, h (x * y) = h x := fun x hx y hy =>
    huv (Set.mk_mem_prod (hΓu hx) hy)
  have : CompactSpace Γ := isCompact_iff_compactSpace.mp hΓc
  obtain ⟨V', hV'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hvo.preimage continuous_subtype_val : IsOpen ((Subtype.val : Γ → G) ⁻¹' v))
    (show ((1 : Γ) : G) ∈ v from h1v rfl)
  let k : Subgroup G := V'.toOpenSubgroup.toSubgroup.map Γ.subtype
  have hko : IsOpen (k : Set G) := by
    rw [Subgroup.coe_map]; exact hΓo.isOpenMap_subtype_val _ V'.toOpenSubgroup.isOpen
  have hkΓ : k ≤ Γ := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hkv : ∀ y ∈ k, y ∈ v := by rintro _ ⟨x, hx, rfl⟩; exact hV' hx
  have hkcl : IsClosed (k : Set G) := Subgroup.isClosed_of_isOpen k hko
  have hkc : IsCompact (k : Set G) := hΓc.of_isClosed_subset hkcl hkΓ
  have hann : (LCAGroup.annihilator k : Set (PontryaginDual G)) = annihilator k := rfl
  have hanno : IsOpen (annihilator k) := by
    rw [← hann]; exact (LCAGroup.isCompact_iff_isOpen_annihilator G k hkcl).mp hkc
  have hannc : IsCompact (annihilator k) := by
    rw [← hann]; exact LCAGroup.isCompact_annihilator_of_isOpen G k hko
  have h1ann : (1 : PontryaginDual G) ∈ annihilator k := fun _ _ => rfl
  have hs : IsStructuralPair Γ k := by
    refine ⟨hΓo, ⟨Γ, hΓc, subset_rfl, ⟨univ, univ_mem, inter_subset_right⟩, Subgroup.closure_eq Γ⟩,
      ⟨hkcl, hanno, LCAGroup.annihilator k, hann, ?_⟩, hkΓ⟩
    refine ⟨annihilator k, hannc, hann.ge, ⟨annihilator k, hanno.mem_nhds h1ann, inter_subset_left⟩, ?_⟩
    rw [← hann, Subgroup.closure_eq]
  obtain ⟨m, n, r, s, d, π, hπ⟩ := exists_elemPresentation_of_isStructuralPair G Γ k hs
  have hker : ∀ x : Γ, π x = 1 ↔ (x : G) ∈ k := hπ.2.2.2.2
  have hsurj : Function.Surjective π := hπ.2.2.2.1
  let k' : Subgroup Γ := k.comap Γ.subtype
  have hk'o : IsOpen (k' : Set Γ) := hko.preimage continuous_subtype_val
  have : Finite (Γ ⧸ k') := Subgroup.quotient_finite_of_isOpen k' hk'o
  have hle : k' ≤ π.ker := fun x hx => (hker x).2 hx
  have hfin : Finite (ElemGroup m n r s d) := by
    refine Finite.of_surjective
      (fun q : Γ ⧸ k' => Multiplicative.toAdd (QuotientGroup.lift k' π hle q)) ?_
    intro e
    obtain ⟨x, hx⟩ := hsurj (Multiplicative.ofAdd e)
    exact ⟨(x : Γ ⧸ k'), by simp [QuotientGroup.lift_mk, hx]⟩
  obtain ⟨rfl, rfl, rfl⟩ := elem_dims_zero hfin
  let sec : Multiplicative (ElemGroup 0 0 0 s d) → Γ := Function.surjInv hsurj
  let g : ElemGroup 0 0 0 s d → ℂ := fun e => h (sec (Multiplicative.ofAdd e))
  have hg : IsRapidDecay g := rapidDecay_of_finite g
  let gs : ElemSchwartz 0 0 0 s d := ⟨g, Submodule.subset_span hg⟩
  refine Submodule.subset_span ⟨Γ, k, 0, 0, 0, s, d, π, gs, hs, hπ, ?_⟩
  funext x
  by_cases hx : x ∈ Γ
  · unfold extendPullback
    rw [dif_pos hx]
    show h x = h (sec (Multiplicative.ofAdd (Multiplicative.toAdd (π ⟨x, hx⟩))))
    rw [ofAdd_toAdd]
    have hy : π (sec (π ⟨x, hx⟩)) = π ⟨x, hx⟩ := Function.surjInv_eq hsurj _
    have hmem : (((⟨x, hx⟩ : Γ)⁻¹ * sec (π ⟨x, hx⟩) : Γ) : G) ∈ k := by
      rw [← hker, map_mul, map_inv, hy, inv_mul_cancel]
    have := hinv x hx _ (hkv _ hmem)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
    exact this.symm
  · unfold extendPullback
    rw [dif_neg hx]
    exact image_eq_zero_of_notMem_tsupport (fun h' => hx (hsupp h'))

end Generic


section Adele

variable (F : Type*) [Field F] [NumberField F]

/-- The finite adeles as a restricted product. -/
abbrev FinAd : Type _ :=
  Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]

/-- The additive group of the finite adeles, written multiplicatively. -/
abbrev GA : Type _ := Multiplicative (FiniteAdeleRing (𝓞 F) F)

theorem t2_GA : T2Space (GA F) := inferInstanceAs (T2Space (FinAd F))

theorem td_GA : TotallyDisconnectedSpace (GA F) := by
  have hinj : Function.Injective
      (fun x : FinAd F => (x : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)) :=
    fun x y hxy => Subtype.ext hxy
  have : TotallyDisconnectedSpace (FinAd F) :=
    ⟨isTotallyDisconnected_of_image RestrictedProduct.continuous_coe.continuousOn hinj
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  exact inferInstanceAs (TotallyDisconnectedSpace (FinAd F))

theorem mem_integers_iff (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F) :
    z ∈ v.adicCompletionIntegers F ↔ ‖z‖ ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans
    Valued.toNormedField.norm_le_one_iff.symm

/-- Every compact subset of `𝔸_F^f` lies in a compact open subgroup. -/
theorem exists_compactOpen (C : Set (GA F)) (hC : IsCompact C) :
    ∃ H : Subgroup (GA F), IsOpen (H : Set (GA F)) ∧ IsCompact (H : Set (GA F)) ∧ C ⊆ H := by
  classical
  let pf : GA F → FinAd F := fun x => Multiplicative.toAdd x
  have hpf : Continuous pf := continuous_toAdd
  have hH : IsCompact (pf '' C) := hC.image hpf
  have hA : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      IsCompact ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∧
        IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Filter.Eventually.of_forall fun v =>
      ⟨isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F))),
        Valued.isOpen_valuationSubring _⟩
  obtain ⟨B, hBc, hBcof, hBmem⟩ :=
    (RiemannMasullo.isCompact_closure_restrictedProduct_iff hA (pf '' C)).mp
      (by rw [hH.isClosed.closure_eq]; exact hH)
  have hbd : ∀ v, ∃ c : ℝ, ∀ z ∈ B v, ‖z‖ ≤ c := fun v => (hBc v).isBounded.exists_norm_le
  choose c hc using hbd
  let Rv : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if B v = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) then 1 else max (c v) 1
  have hRv1 : ∀ v, 1 ≤ Rv v := fun v => by
    simp only [Rv]; split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  have hHR : ∀ z ∈ pf '' C, ∀ v, ‖z v‖ ≤ Rv v := by
    intro z hz v
    by_cases hv : B v = (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    · have h1 := hBmem z hz v
      rw [hv] at h1
      simp only [Rv, hv, if_true]
      exact (mem_integers_iff F v _).1 h1
    · simp only [Rv, hv, if_false]
      exact (hc v _ (hBmem z hz v)).trans (le_max_left _ _)
  let Γ' : Subgroup (GA F) :=
    { carrier := {x | ∀ v, ‖pf x v‖ ≤ Rv v}
      mul_mem' := fun {a b} ha hb v => by
        have : pf (a * b) v = pf a v + pf b v := rfl
        show ‖pf (a * b) v‖ ≤ Rv v
        rw [this]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha v) (hb v))
      one_mem' := fun v => by
        have : pf 1 v = 0 := rfl
        show ‖pf 1 v‖ ≤ Rv v
        rw [this, norm_zero]; exact zero_le_one.trans (hRv1 v)
      inv_mem' := fun {a} ha v => by
        have : pf a⁻¹ v = - pf a v := rfl
        show ‖pf a⁻¹ v‖ ≤ Rv v
        rw [this, norm_neg]; exact ha v }
  have hCΓ' : C ⊆ Γ' := fun x hx v => hHR (pf x) ⟨x, hx, rfl⟩ v
  let W : Set (FinAd F) := {z | ∀ v, ‖z v‖ ≤ Rv v}
  have hWcl : IsClosed W := by
    have : W = ⋂ v, {z : FinAd F | ‖z v‖ ≤ Rv v} := by
      ext z; simp [W]
    rw [this]
    exact isClosed_iInter fun v =>
      isClosed_le ((RestrictedProduct.continuous_eval v).norm) continuous_const
  have hWc : IsCompact W := by
    have := (RiemannMasullo.isCompact_closure_restrictedProduct_iff hA W).mpr
      ⟨fun v => Metric.closedBall 0 (Rv v), fun v => isCompact_closedBall 0 _, ?_,
        fun z hz v => mem_closedBall_zero_iff.mpr (hz v)⟩
    · rwa [hWcl.closure_eq] at this
    · filter_upwards [hBcof] with v hv
      have : Rv v = 1 := by simp [Rv, hv]
      rw [this]; ext z; rw [mem_closedBall_zero_iff]; exact (mem_integers_iff F v z).symm
  have hΓ'c : IsCompact (Γ' : Set (GA F)) := by
    have : (Γ' : Set (GA F)) = (fun z : FinAd F => (Multiplicative.ofAdd z : GA F)) '' W := by
      ext x
      constructor
      · intro hx; exact ⟨pf x, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩; exact hz
    rw [this]
    exact hWc.image continuous_ofAdd
  have hΓ'o : IsOpen (Γ' : Set (GA F)) := by
    have hOo : IsOpen {x : GA F | ∀ v, (pf x).1 v ∈ v.adicCompletionIntegers F} :=
      (RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)).preimage hpf
    refine Subgroup.isOpen_of_mem_nhds Γ' (g := 1) (Filter.mem_of_superset (hOo.mem_nhds ?_) ?_)
    · intro v; exact zero_mem _
    · intro x hx v; exact ((mem_integers_iff F v _).1 (hx v)).trans (hRv1 v)
  exact ⟨Γ', hΓ'o, hΓ'c, hCΓ'⟩

theorem lc_GA : LocallyCompactSpace (GA F) := by
  obtain ⟨H, hHo, hHc, h1⟩ := exists_compactOpen F {1} isCompact_singleton
  exact hHc.locallyCompactSpace_of_mem_nhds_of_group (hHo.mem_nhds (h1 rfl))

end Adele

end Sol_MasulloGRH_schwartzBruhat_finiteAdeleRing_range_eq

open Sol_MasulloGRH_schwartzBruhat_finiteAdeleRing_range_eq in
open MasulloGRH in
theorem solution
    (F : Type*) [Field F] [NumberField F] :
    Set.range (fun (f : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F)))
        (x : FiniteAdeleRing (𝓞 F) F) => f (Multiplicative.ofAdd x)) =
      {h : FiniteAdeleRing (𝓞 F) F → ℂ | IsLocallyConstant h ∧ HasCompactSupport h} := by
  have := t2_GA F
  have := td_GA F
  have := lc_GA F
  have hb := exists_compactOpen F
  ext h
  constructor
  · rintro ⟨f, rfl⟩
    exact range_sub hb f
  · rintro ⟨hlc, hcs⟩
    exact ⟨⟨fun x => h (Multiplicative.toAdd x), mem_of_lc hb hlc hcs⟩, rfl⟩
