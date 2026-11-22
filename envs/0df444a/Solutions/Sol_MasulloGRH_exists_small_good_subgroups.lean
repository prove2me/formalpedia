-- Prove2me | solution 1 for MasulloGRH.exists_small_good_subgroups
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T14:34:53.685267+00:00
-- url     : https://prove2.me/submissions/ac89976e-7b1b-422a-b65b-cfd1ab6a2260

import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_compactlyGenerated_exists_elemQuotient
import Theorems.Thm_MasulloGRH_annihilator_isCompactlyGenerated

set_option autoImplicit false

namespace Aux_SG

open MasulloGRH Topology Set Filter

lemma circle_nss (z : UnitAddCircle) (h : ∀ k : ℕ, ‖k • z‖ < 1 / 4) : z = 0 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, |t| ≤ 1 / 2 ∧ (t : UnitAddCircle) = z := by
    refine ⟨(AddCircle.equivIoc 1 (-1 / 2) z : ℝ), ?_, ?_⟩
    · have h1 := (AddCircle.equivIoc 1 (-1 / 2) z).2
      rw [abs_le]
      constructor
      · linarith [h1.1]
      · linarith [h1.2]
    · exact (AddCircle.equivIoc 1 (-1 / 2)).symm_apply_apply z
  have hn : ∀ x : ℝ, |x| ≤ 1 / 2 → ‖(x : UnitAddCircle)‖ = |x| := fun x hx =>
    (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).2 (by simpa using hx)
  by_contra hz
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hz (by simp)
  have hpos : 0 < |t| := abs_pos.2 ht0
  have h1 := h 1
  rw [one_smul, hn t ht] at h1
  set k := Nat.ceil (1 / (4 * |t|)) with hkdef
  have hk1 : 1 / (4 * |t|) ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < 1 / (4 * |t|) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hA : 1 / 4 ≤ (k : ℝ) * |t| := by
    have := mul_le_mul_of_nonneg_right hk1 hpos.le
    have e : 1 / (4 * |t|) * |t| = 1 / 4 := by field_simp
    linarith
  have hB : (k : ℝ) * |t| < 1 / 2 := by
    have := mul_lt_mul_of_pos_right hk2 hpos
    have e : (1 / (4 * |t|) + 1) * |t| = 1 / 4 + |t| := by field_simp
    linarith
  have hk := h k
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul, hn _ (by rw [abs_mul, Nat.abs_cast]; linarith),
    abs_mul, Nat.abs_cast] at hk
  linarith

lemma elem_nss (m n r s : ℕ) (d : Fin s → ℕ) :
    ∃ V ∈ 𝓝 (0 : ElemGroup m n r s d),
      ∀ x : ElemGroup m n r s d, (∀ k : ℕ, k • x ∈ V) → x = 0 := by
  refine ⟨Metric.ball (0 : Fin m → ℝ) 1 ×ˢ (Metric.ball (0 : Fin n → UnitAddCircle) (1 / 4) ×ˢ
    (({0} : Set (Fin r → ℤ)) ×ˢ ({0} : Set ((i : Fin s) → ZMod (d i))))), ?_, ?_⟩
  · refine prod_mem_nhds (Metric.ball_mem_nhds _ one_pos)
      (prod_mem_nhds (Metric.ball_mem_nhds _ (by norm_num)) (prod_mem_nhds ?_ ?_))
    · exact (isOpen_discrete _).mem_nhds rfl
    · exact (isOpen_discrete _).mem_nhds rfl
  · rintro ⟨a, b, c, e⟩ h
    have ha : a = 0 := by
      by_contra ha
      have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / ‖a‖)
      have h1 : ‖k • a‖ < 1 := by
        have := (h k).1
        simpa [Metric.mem_ball, dist_zero_right] using this
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast] at h1
      rw [div_lt_iff₀ hpos] at hk
      linarith
    have hb : b = 0 := by
      funext j
      refine circle_nss (b j) fun k => ?_
      have h1 : ‖k • b‖ < 1 / 4 := by
        have := (h k).2.1
        simpa [Metric.mem_ball, dist_zero_right] using this
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm (k • b) j) h1
    have hc : c = 0 := by simpa using (h 1).2.2.1
    have he : e = 0 := by simpa using (h 1).2.2.2
    subst ha hb hc he
    rfl

lemma circle_subgroup_nss : ∃ S : Set Circle, IsOpen S ∧ (1 : Circle) ∈ S ∧
    ∀ H : Subgroup Circle, (H : Set Circle) ⊆ S → H = ⊥ := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have he : ∀ t : UnitAddCircle, e t = AddCircle.toCircle t := fun t =>
    AddCircle.homeomorphCircle_apply _ t
  have he0 : e 0 = 1 := by
    rw [he]
    simpa using AddCircle.toCircle_nsmul (0 : UnitAddCircle) 0
  refine ⟨e '' Metric.ball 0 (1 / 4), e.isOpenMap _ Metric.isOpen_ball,
    ⟨0, Metric.mem_ball_self (by norm_num), he0⟩, ?_⟩
  intro H hH
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨t, -, rfl⟩ := hH hz
  have ht : t = 0 := by
    apply circle_nss
    intro j
    obtain ⟨t', ht', hte⟩ := hH (H.pow_mem hz j)
    have : t' = j • t := by
      apply e.injective
      rw [hte, he, he, AddCircle.toCircle_nsmul]
    subst this
    simpa [Metric.mem_ball, dist_zero_right] using ht'
  subst ht
  rw [he0]
  exact Subgroup.one_mem _

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma annihilator_open {k : Subgroup G} (hk : IsCompact (k : Set G))
    (A : Subgroup (PontryaginDual G)) (hA : (A : Set (PontryaginDual G)) = annihilator k) :
    IsOpen (annihilator k) := by
  obtain ⟨S, hSo, hS1, hSH⟩ := circle_subgroup_nss
  rw [← hA]
  apply Subgroup.isOpen_of_mem_nhds A (g := 1)
  have hO : IsOpen {χ : PontryaginDual G | MapsTo χ k S} :=
    (ContinuousMap.isOpen_setOfPred_mapsTo hk hSo).preimage
      (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
  refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
  · intro x _
    exact hS1
  · intro χ hχ
    have : χ ∈ (A : Set (PontryaginDual G)) := by
      rw [hA]
      intro x hx
      have hbot := hSH (k.map χ.toMonoidHom) (by
        rintro _ ⟨y, hy, rfl⟩
        exact hχ hy)
      have hm : χ.toMonoidHom x ∈ k.map χ.toMonoidHom := ⟨x, hx, rfl⟩
      rw [hbot] at hm
      exact hm
    exact this

lemma pair_nss' {Γ k : Subgroup G} {m n r s : ℕ} {d : Fin s → ℕ}
    {π : ↥Γ →* Multiplicative (ElemGroup m n r s d)} (hΓ : IsOpen (Γ : Set G))
    (hkΓ : k ≤ Γ) (hπ : IsElemPresentation Γ k π) :
    ∃ W ∈ 𝓝 (1 : G), (∀ H : Subgroup G, (H : Set G) ⊆ W → H ≤ k) ∧
      ∀ w ∈ W, ∀ x ∈ k, w * x ∈ W := by
  obtain ⟨V, hV, hVx⟩ := elem_nss m n r s d
  let O : Set ↥Γ := {y | Multiplicative.toAdd (π y) ∈ V}
  have hO : O ∈ 𝓝 (1 : ↥Γ) := by
    have hc : Continuous (fun y : ↥Γ => Multiplicative.toAdd (π y)) :=
      continuous_toAdd.comp hπ.2.1
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV)
  refine ⟨Subtype.val '' O, ?_, ?_, ?_⟩
  · exact hΓ.isOpenMap_subtype_val.image_mem_nhds hO
  · intro H hH x hx
    obtain ⟨y, -, rfl⟩ := hH hx
    have h0 : Multiplicative.toAdd (π y) = 0 := by
      apply hVx
      intro j
      obtain ⟨z, hzO, hz⟩ := hH (H.pow_mem hx j)
      have hzy : z = y ^ j := Subtype.ext (by simp [hz])
      subst hzy
      have h2 : Multiplicative.toAdd (π (y ^ j)) ∈ V := hzO
      simpa [map_pow, toAdd_pow] using h2
    exact (hπ.2.2.2.2 y).1 (by simpa using h0)
  · rintro _ ⟨y, hy, rfl⟩ x hx
    let z : ↥Γ := ⟨x, hkΓ hx⟩
    have hz : π z = 1 := (hπ.2.2.2.2 z).2 hx
    refine ⟨y * z, ?_, rfl⟩
    have h2 : Multiplicative.toAdd (π y) ∈ V := hy
    show Multiplicative.toAdd (π (y * z)) ∈ V
    rw [map_mul, hz, mul_one]
    exact h2

lemma sub_hcg {Γ : Subgroup G} (hΓ : IsOpen (Γ : Set G)) (hcg : IsCompactlyGeneratedSubgroup Γ) :
    ∃ C : Set ↥Γ, IsCompact C ∧ Subgroup.closure C = ⊤ := by
  obtain ⟨U, hUc, -, -, hcl⟩ := hcg
  have hcl' : IsClosed (Γ : Set G) := Subgroup.isClosed_of_isOpen Γ hΓ
  subst hcl
  exact ⟨_, hcl'.isClosedEmbedding_subtypeVal.isCompact_preimage hUc,
    Subgroup.closure_closure_coe_preimage⟩

end Aux_SG

open MasulloGRH Topology Set Filter in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ k : ℕ → Subgroup G, Antitone k ∧ (∀ U ∈ nhds (1 : G), ∃ N, (k N : Set G) ⊆ U) ∧
      (∀ N, IsGoodSubgroup (k N)) ∧
      ∀ (N : ℕ) (Γ : Subgroup G), IsOpen (Γ : Set G) → IsCompactlyGeneratedSubgroup Γ →
        k N ≤ Γ → ∃ (m n r s : ℕ) (d : Fin s → ℕ)
          (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)), IsElemPresentation Γ (k N) π := by
  -- an open compactly generated subgroup Γ₀
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  set Γ₀ : Subgroup G := Subgroup.closure V with hΓ₀def
  have hVΓ₀ : V ⊆ Γ₀ := Subgroup.subset_closure
  have hΓ₀o : IsOpen (Γ₀ : Set G) :=
    Subgroup.isOpen_of_mem_nhds Γ₀ (Filter.mem_of_superset hV hVΓ₀)
  have hΓ₀cg : IsCompactlyGeneratedSubgroup Γ₀ :=
    ⟨V, hVc, hVΓ₀, ⟨V, hV, inter_subset_left⟩, rfl⟩
  -- general facts about open compactly generated subgroups
  have hLC : ∀ Γ : Subgroup G, IsOpen (Γ : Set G) → LocallyCompactSpace ↥Γ := fun Γ hΓ =>
    hΓ.locallyCompactSpace
  have hSC : ∀ Γ : Subgroup G, SecondCountableTopology ↥Γ := fun Γ =>
    TopologicalSpace.Subtype.secondCountableTopology (Γ : Set G)
  let P : Subgroup G → Prop := fun k => IsCompact (k : Set G) ∧ k ≤ Γ₀ ∧
    ∃ (m n r s : ℕ) (d : Fin s → ℕ) (π : ↥Γ₀ →* Multiplicative (ElemGroup m n r s d)),
      IsElemPresentation Γ₀ k π
  have step : ∀ U ∈ 𝓝 (1 : G), ∃ k, P k ∧ (k : Set G) ⊆ U := by
    intro U hU
    haveI := hLC Γ₀ hΓ₀o
    haveI := hSC Γ₀
    have hU' : (Subtype.val ⁻¹' U : Set ↥Γ₀) ∈ 𝓝 (1 : ↥Γ₀) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨K, hKc, hKU, m, n, r, s, d, π, hd, hπc, hπo, hπs, hπk⟩ :=
      compactlyGenerated_exists_elemQuotient ↥Γ₀ (Aux_SG.sub_hcg hΓ₀o hΓ₀cg) _ hU'
    refine ⟨K.map Γ₀.subtype, ⟨hKc.image continuous_subtype_val, Subgroup.map_subtype_le K,
      m, n, r, s, d, π, hd, hπc, hπo, hπs, fun x => ?_⟩, ?_⟩
    · rw [hπk]
      exact (Subgroup.mem_map_iff_mem Γ₀.subtype_injective).symm
    · rintro _ ⟨y, hy, rfl⟩
      exact hKU hy
  choose stepK hstepP hstepU using step
  have nssP : ∀ k, P k → ∃ W ∈ 𝓝 (1 : G), (∀ H : Subgroup G, (H : Set G) ⊆ W → H ≤ k) ∧
      ∀ w ∈ W, ∀ x ∈ k, w * x ∈ W := by
    rintro k ⟨-, hkΓ, m, n, r, s, d, π, hπ⟩
    exact Aux_SG.pair_nss' hΓ₀o hkΓ hπ
  choose Wf hWf hWfk hWfm using nssP
  obtain ⟨u, hu⟩ := (𝓝 (1 : G)).exists_antitone_basis
  have hu0 : ∀ N, u N ∈ 𝓝 (1 : G) := fun N => hu.mem N
  let seq : ℕ → {k : Subgroup G // P k} := fun N =>
    Nat.rec (motive := fun _ => {k : Subgroup G // P k}) ⟨stepK (u 0) (hu0 0), hstepP _ _⟩
      (fun N prev => ⟨stepK (u (N + 1) ∩ Wf prev.1 prev.2)
        (inter_mem (hu0 _) (hWf _ _)), hstepP _ _⟩) N
  let k : ℕ → Subgroup G := fun N => (seq N).1
  have hkP : ∀ N, P (k N) := fun N => (seq N).2
  have hk_succ : ∀ N, (k (N + 1) : Set G) ⊆ u (N + 1) ∩ Wf (k N) (hkP N) := fun N =>
    hstepU _ _
  have hk_u : ∀ N, (k N : Set G) ⊆ u N := by
    intro N
    cases N with
    | zero => exact hstepU _ _
    | succ N => exact (hk_succ N).trans inter_subset_left
  have hanti : Antitone k := by
    refine antitone_nat_of_succ_le fun N => ?_
    exact hWfk _ _ _ ((hk_succ N).trans inter_subset_right)
  refine ⟨k, hanti, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨N, -, hN⟩ := hu.toHasBasis.mem_iff.1 hU
    exact ⟨N, (hk_u N).trans hN⟩
  · intro N
    obtain ⟨hkc, hkΓ, m, n, r, s, d, π, hπ⟩ := hkP N
    obtain ⟨A, hA, hAcg⟩ :=
      annihilator_isCompactlyGenerated G (k N) Γ₀ hkc hΓ₀o hkΓ π hπ
    exact ⟨hkc.isClosed, Aux_SG.annihilator_open hkc A hA, A, hA, hAcg⟩
  · intro N Γ hΓ hΓcg hkΓ
    have hkc : IsCompact (k N : Set G) := (hkP N).1
    obtain ⟨W, hW, hWH, hWm⟩ := Aux_SG.pair_nss' hΓ₀o (hkP N).2.1
      (hkP N).2.2.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    haveI := hLC Γ hΓ
    haveI := hSC Γ
    let L : Subgroup ↥Γ := (k N).subgroupOf Γ
    haveI hLcl : IsClosed (L : Set ↥Γ) := by
      rw [Subgroup.coe_subgroupOf]
      exact hkc.isClosed.preimage continuous_subtype_val
    let q : ↥Γ →* ↥Γ ⧸ L := QuotientGroup.mk' L
    have hq : ∀ y, q y = (y : ↥Γ ⧸ L) := fun _ => rfl
    have hQcg : ∃ C : Set (↥Γ ⧸ L), IsCompact C ∧ Subgroup.closure C = ⊤ := by
      obtain ⟨C, hCc, hCcl⟩ := Aux_SG.sub_hcg hΓ hΓcg
      refine ⟨q '' C, hCc.image QuotientGroup.continuous_mk, ?_⟩
      rw [← MonoidHom.map_closure, hCcl, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective L
    have hUQ : q '' (Subtype.val ⁻¹' W : Set ↥Γ) ∈ 𝓝 (1 : ↥Γ ⧸ L) := by
      have h1 : (Subtype.val ⁻¹' W : Set ↥Γ) ∈ 𝓝 (1 : ↥Γ) :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hW)
      exact QuotientGroup.isOpenMap_coe.image_mem_nhds h1
    obtain ⟨K, -, hKU, m, n, r, s, d, π', hd, hπc, hπo, hπs, hπk⟩ :=
      compactlyGenerated_exists_elemQuotient (↥Γ ⧸ L) hQcg _ hUQ
    -- `K` is trivial
    have hKtriv : ∀ z ∈ K, z = 1 := by
      let Hs : Subgroup G := (K.comap q).map Γ.subtype
      have hHs : (Hs : Set G) ⊆ W := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨w, hw, hwy⟩ := hKU hy
        have hmem : w⁻¹ * y ∈ L := QuotientGroup.eq.1 hwy
        have := hWm _ hw _ ((Subgroup.mem_subgroupOf).1 hmem)
        simpa using this
      have hle := hWH Hs hHs
      intro z hz
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective L z
      have hy : (y : G) ∈ k N := hle ⟨y, hz, rfl⟩
      exact (QuotientGroup.eq_one_iff y).2 ((Subgroup.mem_subgroupOf).2 hy)
    refine ⟨m, n, r, s, d, π'.comp q, hd, hπc.comp QuotientGroup.continuous_mk,
      hπo.comp QuotientGroup.isOpenMap_coe, hπs.comp (QuotientGroup.mk'_surjective L), ?_⟩
    intro y
    rw [MonoidHom.comp_apply, hπk]
    constructor
    · intro h
      have := hKtriv _ h
      exact (Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff y).1 this)
    · intro h
      have : q y = 1 := (QuotientGroup.eq_one_iff y).2 ((Subgroup.mem_subgroupOf).2 h)
      rw [this]
      exact K.one_mem
