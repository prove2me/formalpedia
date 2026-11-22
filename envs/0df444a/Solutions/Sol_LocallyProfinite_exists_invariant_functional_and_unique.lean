-- Prove2me | solution 1 for LocallyProfinite.exists_invariant_functional_and_unique
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:29:46.969936+00:00
-- url     : https://prove2.me/submissions/34e01e53-134b-4b5f-9f26-62bbc53b126e

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace Sol_LocallyProfinite_exists_invariant_functional_and_unique

open MeasureTheory

section Aux

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Group G] [IsTopologicalGroup G] in
/-- The indicator of a clopen set is locally constant. -/
lemma isLocallyConstant_indicator {U : Set G} (hU : IsClopen U) (c : ℂ) :
    IsLocallyConstant (U.indicator fun _ => c) := fun s => by
  rw [Set.indicator_preimage, Set.ite, Set.sdiff_eq]
  exact ((IsLocallyConstant.const c s).inter hU.isOpen).union
    ((IsLocallyConstant.const (0 : ℂ) s).inter hU.compl.isOpen)

/-- A locally constant function with compact support is uniformly right-invariant under a
neighbourhood of `1`. -/
lemma exists_nhds_one_mul_eq {F : G → ℂ} (hF : IsLocallyConstant F) (hc : HasCompactSupport F) :
    ∃ U ∈ 𝓝 (1 : G), ∀ x : G, ∀ u ∈ U, F (x * u) = F x := by
  set n : Set (G × G) := {p | F (p.1 * p.2) = F p.1} with hn_def
  have hn : IsOpen n := by
    have h1 : IsLocallyConstant (fun p : G × G => F (p.1 * p.2) - F p.1) :=
      IsLocallyConstant.comp₂ (hF.comp_continuous continuous_mul)
        (hF.comp_continuous continuous_fst) (· - ·)
    have := h1.isOpen_fiber 0
    simpa [sub_eq_zero, n] using this
  have hsub : tsupport F ×ˢ ({1} : Set G) ⊆ n := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    simp only [Set.mem_singleton_iff] at hy
    simp [n, hy]
  obtain ⟨u, v, -, hv, hsu, h1v, huv⟩ := generalized_tube_lemma hc isCompact_singleton hn hsub
  have hv1 : v ∈ 𝓝 (1 : G) := hv.mem_nhds (h1v rfl)
  refine ⟨v ∩ v⁻¹, inter_mem hv1 (inv_mem_nhds_one G hv1), ?_⟩
  rintro x w ⟨hwv, hwv'⟩
  by_cases hx : x ∈ tsupport F
  · exact huv (Set.mk_mem_prod (hsu hx) hwv)
  by_cases hxw : x * w ∈ tsupport F
  · have := huv (Set.mk_mem_prod (hsu hxw) (show w⁻¹ ∈ v from hwv'))
    simp only [n, Set.mem_ofPred_eq, mul_inv_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxw]

/-- The subgroup of right translations fixing a function. -/
def rStab (F : G → ℂ) : Subgroup G where
  carrier := {g | ∀ x, F (x * g) = F x}
  one_mem' := fun x => by simp
  mul_mem' := fun {a b} ha hb x => by
    show F (x * (a * b)) = F x
    rw [← mul_assoc, hb, ha]
  inv_mem' := fun {a} ha x => by
    have := ha (x * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

lemma rStab_mem_nhds {F : G → ℂ} (hF : IsLocallyConstant F) (hc : HasCompactSupport F) :
    (rStab F : Set G) ∈ 𝓝 (1 : G) := by
  obtain ⟨U, hU, h⟩ := exists_nhds_one_mul_eq hF hc
  exact mem_of_superset hU (fun u hu x => h x u hu)

/-- A compactly supported function invariant under right translation by an open subgroup `K`
is a finite linear combination of indicators of left cosets of `K`. -/
lemma coset_decomp (K : Subgroup G) (hK : IsOpen (K : Set G)) {F : G → ℂ}
    (hc : HasCompactSupport F) (hF : ∀ x, ∀ k ∈ K, F (x * k) = F x) :
    ∃ T : Finset (G ⧸ K), ∀ x, F x =
      ∑ c ∈ T, F c.out * (K : Set G).indicator (fun _ => (1 : ℂ)) (c.out⁻¹ * x) := by
  classical
  have := QuotientGroup.discreteTopology hK
  have hcont : Continuous ((↑) : G → G ⧸ K) := continuous_quot_mk
  have hfin : (((↑) : G → G ⧸ K) '' tsupport F).Finite :=
    (hc.image hcont).finite_of_discrete
  refine ⟨hfin.toFinset, fun x => ?_⟩
  have key : ∀ c : G ⧸ K, F c.out * (K : Set G).indicator (fun _ => (1 : ℂ)) (c.out⁻¹ * x) =
      if c = (x : G ⧸ K) then F c.out else 0 := by
    intro c
    have hiff : c.out⁻¹ * x ∈ K ↔ c = (x : G ⧸ K) := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    by_cases h : c = (x : G ⧸ K)
    · rw [if_pos h, Set.indicator_of_mem (show c.out⁻¹ * x ∈ (K : Set G) from hiff.2 h), mul_one]
    · rw [if_neg h, Set.indicator_of_notMem (show c.out⁻¹ * x ∉ (K : Set G) from
        fun h' => h (hiff.1 h')), mul_zero]
  rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_ite_eq']
  by_cases hx : (x : G ⧸ K) ∈ hfin.toFinset
  · rw [if_pos hx]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
    rw [hh, hF x h h.2]
  · rw [if_neg hx]
    have : x ∉ tsupport F := fun hx' => hx (hfin.mem_toFinset.2 ⟨x, hx', rfl⟩)
    exact image_eq_zero_of_notMem_tsupport this

end Aux

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : Submodule ℂ (G → ℂ))

/-- Left invariance of a linear functional on `V`. -/
def IsInv (φ : V →ₗ[ℂ] ℂ) : Prop :=
  ∀ (g : G) (f f' : V), (∀ x : G, (f' : G → ℂ) x = (f : G → ℂ) (g * x)) → φ f' = φ f

variable {V}

lemma transl_mem (hV : ∀ f : G → ℂ, f ∈ V ↔ IsLocallyConstant f ∧ HasCompactSupport f)
    {f : G → ℂ} (hf : f ∈ V) (g : G) : (fun x => f (g * x)) ∈ V := by
  obtain ⟨h1, h2⟩ := (hV f).1 hf
  exact (hV _).2 ⟨h1.comp_continuous (continuous_const_mul g),
    h2.comp_homeomorph (Homeomorph.mulLeft g)⟩

/-- Key step: on functions right-invariant under an open subgroup `K`, every invariant functional
is determined by its value on the indicator of `K`, through a coefficient independent of the
functional. -/
lemma key (hV : ∀ f : G → ℂ, f ∈ V ↔ IsLocallyConstant f ∧ HasCompactSupport f)
    (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hK1 : (K : Set G).indicator (fun _ => (1 : ℂ)) ∈ V)
    (F : V) (hF : ∀ x, ∀ k ∈ K, (F : G → ℂ) (x * k) = (F : G → ℂ) x) :
    ∃ s : ℂ, ∀ φ : V →ₗ[ℂ] ℂ, IsInv V φ → φ F = s * φ ⟨_, hK1⟩ := by
  obtain ⟨T, hT⟩ := coset_decomp K hKo ((hV _).1 F.2).2 hF
  let e : G → V := fun y =>
    ⟨fun x => (K : Set G).indicator (fun _ => (1 : ℂ)) (y⁻¹ * x), transl_mem hV hK1 y⁻¹⟩
  have hFeq : F = ∑ c ∈ T, (F : G → ℂ) c.out • e c.out := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, e]
    exact hT x
  refine ⟨∑ c ∈ T, (F : G → ℂ) c.out, fun φ hφ => ?_⟩
  have he : ∀ y : G, φ (e y) = φ ⟨_, hK1⟩ := by
    intro y
    refine hφ y⁻¹ ⟨_, hK1⟩ (e y) (fun x => ?_)
    simp [e]
  conv_lhs => rw [hFeq]
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [map_smul, smul_eq_mul, he]

end Main

end Sol_LocallyProfinite_exists_invariant_functional_and_unique

open Sol_LocallyProfinite_exists_invariant_functional_and_unique MeasureTheory in
theorem solution
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (V : Submodule ℂ (G → ℂ))
    (hV : ∀ f : G → ℂ, f ∈ V ↔ IsLocallyConstant f ∧ HasCompactSupport f) :
    ∃ φ₀ : V →ₗ[ℂ] ℂ, φ₀ ≠ 0 ∧
      (∀ (g : G) (f f' : V), (∀ x : G, (f' : G → ℂ) x = (f : G → ℂ) (g * x)) → φ₀ f' = φ₀ f) ∧
      ∀ φ : V →ₗ[ℂ] ℂ,
        (∀ (g : G) (f f' : V), (∀ x : G, (f' : G → ℂ) x = (f : G → ℂ) (g * x)) → φ f' = φ f) →
        ∃ a : ℂ, φ = a • φ₀ := by
  -- a compact open set containing `1`
  obtain ⟨W, hWc, hWo, hW1⟩ : ∃ W : Set G, IsCompact W ∧ IsClopen W ∧ (1 : G) ∈ W := by
    obtain ⟨C, hC, hCn⟩ := exists_compact_mem_nhds (1 : G)
    obtain ⟨W, hW, h1W, hWC⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hCn
    exact ⟨W, hC.of_isClosed_subset hW.1 hWC, hW, h1W⟩
  have hind : ∀ {U : Set G}, IsClopen U → IsCompact U →
      U.indicator (fun _ => (1 : ℂ)) ∈ V := fun {U} hU hUc =>
    (hV _).2 ⟨isLocallyConstant_indicator hU 1,
      HasCompactSupport.intro hUc (fun x hx => Set.indicator_of_notMem hx _)⟩
  let eW : V := ⟨W.indicator (fun _ => (1 : ℂ)), hind hWo hWc⟩
  -- the Haar integral
  let _ : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  have hint : ∀ f : V, Integrable (f : G → ℂ) μ := fun f => by
    obtain ⟨h1, h2⟩ := (hV f).1 f.2
    exact h1.continuous.integrable_of_hasCompactSupport h2
  let φ₀ : V →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, (f : G → ℂ) x ∂μ
      map_add' := fun f g => by
        simp only [Submodule.coe_add, Pi.add_apply]
        exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hφ₀ : ∀ f : V, φ₀ f = ∫ x, (f : G → ℂ) x ∂μ := fun f => rfl
  have hφ₀inv : IsInv V φ₀ := by
    intro g f f' h
    rw [hφ₀, hφ₀, show (f' : G → ℂ) = fun x => (f : G → ℂ) (g * x) from funext h]
    exact integral_mul_left_eq_self _ g
  have hφ₀W : φ₀ eW ≠ 0 := by
    rw [hφ₀]
    show ∫ x, W.indicator (fun _ => (1 : ℂ)) x ∂μ ≠ 0
    rw [integral_indicator_const _ hWo.isOpen.measurableSet]
    have h1 : μ W ≠ 0 := hWo.isOpen.measure_ne_zero μ ⟨1, hW1⟩
    have h2 : μ W ≠ ⊤ := hWc.measure_lt_top.ne
    have h3 : μ.real W ≠ 0 := by
      rw [measureReal_def]
      exact ENNReal.toReal_ne_zero.2 ⟨h1, h2⟩
    rw [Complex.real_smul, mul_one]
    exact_mod_cast h3
  refine ⟨φ₀, fun h => hφ₀W (by rw [h]; rfl), hφ₀inv, fun φ hφ => ?_⟩
  refine ⟨φ eW / φ₀ eW, ?_⟩
  ext f
  -- a compact open subgroup fixing `f` and `eW` under right translation
  have hfV := (hV _).1 f.2
  have heV := (hV _).1 eW.2
  let K : Subgroup G := rStab (f : G → ℂ) ⊓ rStab (eW : G → ℂ)
  have hKn : (K : Set G) ∈ 𝓝 (1 : G) :=
    inter_mem (rStab_mem_nhds hfV.1 hfV.2) (rStab_mem_nhds heV.1 heV.2)
  have hKo : IsOpen (K : Set G) := Subgroup.isOpen_of_mem_nhds K hKn
  have hKcl : IsClosed (K : Set G) := Subgroup.isClosed_of_isOpen K hKo
  have hKW : (K : Set G) ⊆ W := by
    intro g hg
    have h := (Subgroup.mem_inf.1 hg).2 1
    simp only [one_mul] at h
    by_contra hgW
    have h' : (eW : G → ℂ) g = 0 := by
      show W.indicator (fun _ => (1 : ℂ)) g = 0
      exact Set.indicator_of_notMem hgW _
    have h'' : (eW : G → ℂ) 1 = 1 := by
      show W.indicator (fun _ => (1 : ℂ)) 1 = 1
      exact Set.indicator_of_mem hW1 _
    rw [h', h''] at h
    exact zero_ne_one h
  have hKc : IsCompact (K : Set G) := hWc.of_isClosed_subset hKcl hKW
  have hK1 := hind ⟨hKcl, hKo⟩ hKc
  obtain ⟨s, hs⟩ := key hV K hKo hK1 f
    (fun x k hk => (Subgroup.mem_inf.1 hk).1 x)
  obtain ⟨t, ht⟩ := key hV K hKo hK1 eW
    (fun x k hk => (Subgroup.mem_inf.1 hk).2 x)
  have hcross : φ f * φ₀ eW = φ₀ f * φ eW := by
    rw [hs φ hφ, hs φ₀ hφ₀inv, ht φ hφ, ht φ₀ hφ₀inv]
    ring
  rw [LinearMap.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hcross
