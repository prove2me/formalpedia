-- Prove2me | solution 1 for MasulloGRH.exists_fundamentalDomain_normOneIdeles
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T14:18:47.676269+00:00
-- url     : https://prove2.me/submissions/a6382364-c864-4bb7-b862-7975059d6777

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm
import Theorems.Thm_MasulloGRH_tateIdeleDomain_relCompact_and_interior_nonempty
import Theorems.Thm_MasulloGRH_tateIdeleDomain_existsUnique_principal_mul
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff

open NumberField IsDedekindDomain
open scoped NNReal

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_exists_fundamentalDomain_normOneIdeles

open MasulloGRH
open scoped WithZero nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

/-! ### Finite components of an idele -/

/-- The finite component at `v` of an idele times that of its inverse is `1`. -/
lemma fin_mul_inv (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : AdeleRing (𝓞 F) F).2 v * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := g.mul_inv
  have h2 := congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) h
  exact h2

/-- The component of an idele at a finite place `v` has valuation `1` if and only if it and the
`v`-component of the inverse idele are `v`-integral. -/
lemma valued_eq_one_iff (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1 ↔
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
        ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := by
  have hm : Valued.v ((g : AdeleRing (𝓞 F) F).2 v) *
      Valued.v (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
    rw [← map_mul, fin_mul_inv, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro h
    rw [h, one_mul] at hm
    exact ⟨h.le, hm.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    calc (1 : ℤᵐ⁰) = Valued.v ((g : AdeleRing (𝓞 F) F).2 v) *
          Valued.v (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) := hm.symm
      _ ≤ Valued.v ((g : AdeleRing (𝓞 F) F).2 v) * 1 := mul_le_mul' le_rfl h2
      _ = _ := mul_one _

/-- If the `v`-components of an idele and of its inverse are both `v`-integral, the `v`-component
has norm `1`. -/
lemma norm_fin_eq_one_of_mem (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F)
    (h2 : ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) :
    ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have a1 : ‖(g : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h1)
  have a2 : ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h2)
  have hm : ‖(g : AdeleRing (𝓞 F) F).2 v‖ *
      ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    rw [← norm_mul, fin_mul_inv, norm_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ) = ‖(g : AdeleRing (𝓞 F) F).2 v‖ *
        ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ := hm.symm
    _ ≤ ‖(g : AdeleRing (𝓞 F) F).2 v‖ * 1 := mul_le_mul_of_nonneg_left a2 (norm_nonneg _)
    _ = _ := mul_one _

/-- An idele is a unit at all but finitely many finite places. -/
lemma finite_valued_ne_one (g : IdeleGroup F) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v ((g : AdeleRing (𝓞 F) F).2 v) ≠ 1}.Finite := by
  have h1 : ∀ᶠ v in Filter.cofinite,
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := (g : AdeleRing (𝓞 F) F).2.2
  have h2 : ∀ᶠ v in Filter.cofinite,
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F :=
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2.2
  have h3 := h1.and h2
  rw [Filter.eventually_cofinite] at h3
  refine h3.subset ?_
  intro v hv h
  exact hv ((valued_eq_one_iff g v).mpr h)

/-- All but finitely many finite components of an idele have norm `1`. -/
lemma finite_mulSupport_fin (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(g : AdeleRing (𝓞 F) F).2 v‖).Finite := by
  refine (finite_valued_ne_one g).subset ?_
  intro v hv h
  exact hv (norm_fin_eq_one_of_mem g v ((valued_eq_one_iff g v).mp h).1
    ((valued_eq_one_iff g v).mp h).2)

/-! ### The idelic norm -/

/-- The idelic norm is multiplicative. -/
lemma ideleNorm_mul (g h : IdeleGroup F) : ideleNorm (g * h) = ideleNorm g * ideleNorm h := by
  unfold ideleNorm
  have e1 : ∀ w : InfinitePlace F, ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w =
      (g : AdeleRing (𝓞 F) F).1 w * (h : AdeleRing (𝓞 F) F).1 w := fun w => rfl
  have e2 : ∀ v : HeightOneSpectrum (𝓞 F), ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v =
      (g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v := fun v => rfl
  simp only [e1, e2, norm_mul, mul_pow, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (finite_mulSupport_fin g) (finite_mulSupport_fin h)]
  ring


/-- The component at an infinite place `w` of an idele times that of its inverse is `1`. -/
lemma inf_mul_inv (g : IdeleGroup F) (w : InfinitePlace F) :
    (g : AdeleRing (𝓞 F) F).1 w * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1 := by
  have h : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := g.mul_inv
  have h2 := congrArg (fun a : AdeleRing (𝓞 F) F => a.1 w) h
  exact h2


/-- The idelic norm is positive. -/
lemma ideleNorm_pos (g : IdeleGroup F) : 0 < ideleNorm g := by
  unfold ideleNorm
  apply mul_pos
  · refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr ?_) _
    intro h0
    have := inf_mul_inv g w
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · refine finprod_induction (0 < ·) zero_lt_one (fun _ _ => mul_pos) fun v => norm_pos_iff.mpr ?_
    intro h0
    have := fin_mul_inv g v
    rw [h0, zero_mul] at this
    exact zero_ne_one this


/-! ### The archimedean and the finite part of an idele -/

/-- The finite part of an idele. -/
noncomputable def finPart : IdeleGroup F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

/-- The archimedean part of an idele. -/
noncomputable def infPart : IdeleGroup F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

lemma finPart_apply (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    ((finPart g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
      (g : AdeleRing (𝓞 F) F).2 v := rfl

/-! ### Discreteness of the principal ideles -/

omit [NumberField F] in
/-- The norm on the completion at an infinite place restricts to the place on `F`. -/
theorem norm_algebraMap_completion (w : InfinitePlace F) (ξ : F) :
    ‖algebraMap F w.Completion ξ‖ = w ξ := by
  have h := InfinitePlace.Completion.norm_coe (v := w) ((WithAbs.equiv w.1).symm ξ)
  rw [RingEquiv.apply_symm_apply] at h
  exact h

/-- The image of an algebraic integer in the completion at a finite place is integral. -/
theorem valued_algebraMap_le_one (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) x) ≤ (1 : ℤᵐ⁰) := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v x
  exact h.trans_le (v.valuation_le_one x)

/-- An element of the completion `F_v` at a finite place lies in `d⁻¹ 𝒪_v` for some nonzero
`d ∈ 𝒪_F`. -/
theorem exists_ne_zero_valued_mul_le_one (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * x) ≤ (1 : ℤᵐ⁰) := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hπv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) < (1 : ℤᵐ⁰) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v π
    exact h.trans_lt ((v.valuation_lt_one_iff_mem π).2 hπ)
  have hπn : ‖algebraMap (𝓞 F) (v.adicCompletion F) π‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr hπv
  have hpos : (0 : ℝ) < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) hπn
  refine ⟨π ^ n, pow_ne_zero n hπ0, ?_⟩
  rw [← Valued.toNormedField.norm_le_one_iff, map_pow, norm_mul, norm_pow]
  calc ‖algebraMap (𝓞 F) (v.adicCompletion F) π‖ ^ n * ‖x‖
      ≤ (max ‖x‖ 1)⁻¹ * max ‖x‖ 1 :=
        mul_le_mul hn.le (le_max_left _ _) (norm_nonneg _) (inv_pos.mpr hpos).le
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- **Clearing denominators**: for every finite adele `a` there is a nonzero `d ∈ 𝒪_F` such that
`d a` is integral at every finite place. -/
theorem exists_ne_zero_forall_valued_mul_le_one (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * a v) ≤ (1 : ℤᵐ⁰) := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ a v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose dv hdv0 hdv using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_ne_zero_valued_mul_le_one v (a v)
  refine ⟨∏ v ∈ hfin.toFinset, dv v, Finset.prod_ne_zero_iff.mpr fun v _ => hdv0 v, fun v => ?_⟩
  by_cases hv : v ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv, map_mul (algebraMap (𝓞 F) (v.adicCompletion F)),
      mul_right_comm, map_mul]
    exact mul_le_one' (hdv v) (valued_algebraMap_le_one v _)
  · have hav : a v ∈ v.adicCompletionIntegers F := by
      by_contra h
      exact hv (hfin.mem_toFinset.mpr h)
    rw [map_mul]
    exact mul_le_one' (valued_algebraMap_le_one v _)
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hav)

/-- The finite adeles that are integral at every place form an open set. -/
lemma isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

/-- For `d ∈ 𝒪_F`, the ideles `g` such that `d g` is integral at every finite place form an open
subset of the idele group. -/
lemma isOpen_denominatorSet (d : 𝓞 F) :
    IsOpen {g : IdeleGroup F | ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d * (g : AdeleRing (𝓞 F) F).2 v) ≤
        (1 : ℤᵐ⁰)} := by
  have hc : Continuous (fun g : IdeleGroup F =>
      algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d * (g : AdeleRing (𝓞 F) F).2) :=
    continuous_const.mul (continuous_snd.comp Units.continuous_val)
  have h := (isOpen_integral (F := F)).preimage hc
  convert h using 1
  ext g
  refine forall_congr' fun v => ?_
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rfl

/-- **Discreteness of `Fˣ` in the idele group**: a compact subset of `GL₁(𝔸_F)` contains only
finitely many principal ideles. -/
theorem finite_principal_mem_of_isCompact (Q : Set (IdeleGroup F)) (hQ : IsCompact Q) :
    {ξ : Fˣ | principalIdele F ξ ∈ Q}.Finite := by
  classical
  -- a common denominator for the finite components of the elements of `Q`
  have hcover : Q ⊆ ⋃ d : {d : 𝓞 F // d ≠ 0}, {g : IdeleGroup F |
      ∀ v : HeightOneSpectrum (𝓞 F),
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) d.1 * (g : AdeleRing (𝓞 F) F).2 v) ≤
          (1 : ℤᵐ⁰)} := by
    intro g _
    obtain ⟨d, hd0, hd⟩ := exists_ne_zero_forall_valued_mul_le_one (g : AdeleRing (𝓞 F) F).2
    exact Set.mem_iUnion.mpr ⟨⟨d, hd0⟩, hd⟩
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover _ (fun d : {d : 𝓞 F // d ≠ 0} =>
    isOpen_denominatorSet (F := F) d.1) hcover
  let D : 𝓞 F := ∏ i ∈ t, i.1
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => i.2
  have hDF : (algebraMap (𝓞 F) F D) ≠ 0 := by
    simpa using hD0
  have hDQ : ∀ g ∈ Q, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D * (g : AdeleRing (𝓞 F) F).2 v) ≤
        (1 : ℤᵐ⁰) := by
    intro g hg v
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hg)
    obtain ⟨hit, hgi⟩ := Set.mem_iUnion.mp hi
    have hprod : D = i.1 * ∏ j ∈ t.erase i, j.1 := (Finset.mul_prod_erase _ _ hit).symm
    rw [hprod, map_mul (algebraMap (𝓞 F) (v.adicCompletion F)), mul_right_comm, map_mul]
    exact mul_le_one' (hgi v) (valued_algebraMap_le_one v _)
  -- bounded archimedean absolute values
  have h2 : ∀ w : InfinitePlace F, ∃ C : ℝ, ∀ g ∈ Q, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ≤ C := by
    intro w
    have hc : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).1 w) :=
      (continuous_apply w).comp (continuous_fst.comp Units.continuous_val)
    obtain ⟨C, hC⟩ := (hQ.image hc).isBounded.exists_norm_le
    exact ⟨C, fun g hg ↦ hC _ ⟨g, hg, rfl⟩⟩
  choose C hC using h2
  let B : ℝ := ∑ w : InfinitePlace F, w (algebraMap (𝓞 F) F D) * C w
  have hfin := Embeddings.finite_of_norm_le F ℂ B
  have hinj : Set.InjOn (fun ξ : Fˣ ↦ algebraMap (𝓞 F) F D * (ξ : F))
      ((fun ξ : Fˣ ↦ algebraMap (𝓞 F) F D * (ξ : F)) ⁻¹'
        {x : F | IsIntegral ℤ x ∧ ∀ φ : F →+* ℂ, ‖φ x‖ ≤ B}) :=
    ((mul_right_injective₀ hDF).comp Units.val_injective).injOn
  refine (hfin.preimage hinj).subset ?_
  intro ξ hξQ
  have hξQ' : principalIdele F ξ ∈ Q := hξQ
  have hnonneg : ∀ w : InfinitePlace F, 0 ≤ w (algebraMap (𝓞 F) F D) * C w := by
    intro w
    have h := hC w _ hξQ'
    exact mul_nonneg (apply_nonneg _ _) ((norm_nonneg _).trans h)
  refine ⟨?_, fun φ ↦ ?_⟩
  · -- `D ξ` is integral at every finite place
    have hmem : algebraMap (𝓞 F) F D * (ξ : F) ∈ (algebraMap (𝓞 F) F).range := by
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v ↦ ?_
      have h := hDQ _ hξQ' v
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      have e : ((algebraMap (𝓞 F) F D * (ξ : F) : F) : v.adicCompletion F) =
          algebraMap (𝓞 F) (v.adicCompletion F) D *
            ((principalIdele F ξ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v := by
        change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D * (ξ : F)) =
          algebraMap (𝓞 F) (v.adicCompletion F) D * algebraMap F (v.adicCompletion F) (ξ : F)
        rw [map_mul, ← IsScalarTower.algebraMap_apply]
      rw [e]
      exact h
    obtain ⟨z, hz⟩ := hmem
    change IsIntegral ℤ (algebraMap (𝓞 F) F D * (ξ : F))
    rw [← hz]
    exact z.isIntegral_coe
  · -- the archimedean absolute values of `D ξ` are bounded
    have h := hC (InfinitePlace.mk φ) _ hξQ'
    have h' : (InfinitePlace.mk φ) (ξ : F) ≤ C (InfinitePlace.mk φ) := by
      rw [← norm_algebraMap_completion]
      exact h
    calc ‖φ (algebraMap (𝓞 F) F D * (ξ : F))‖
        = (InfinitePlace.mk φ) (algebraMap (𝓞 F) F D) * (InfinitePlace.mk φ) (ξ : F) := by
          rw [← InfinitePlace.apply, map_mul]
      _ ≤ (InfinitePlace.mk φ) (algebraMap (𝓞 F) F D) * C (InfinitePlace.mk φ) :=
          mul_le_mul_of_nonneg_left h' (apply_nonneg _ _)
      _ ≤ B := Finset.single_le_sum (f := fun w : InfinitePlace F ↦
            w (algebraMap (𝓞 F) F D) * C w) (fun w _ ↦ hnonneg w) (Finset.mem_univ _)

/-! ### Ideles with prescribed archimedean norm and prescribed ideal class -/

omit [NumberField F] in
/-- Every positive real number is the norm of an element of the completion at an infinite
place. -/
lemma exists_norm_eq (w : InfinitePlace F) (s : ℝ) (hs : 0 < s) :
    ∃ z : w.Completion, ‖z‖ = s := by
  by_cases hw : w.IsReal
  · obtain ⟨z, hz⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw s
    refine ⟨z, ?_⟩
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) z, hz, Real.norm_eq_abs, abs_of_pos hs]
  · obtain ⟨z, hz⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) (s : ℂ)
    refine ⟨z, ?_⟩
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) z, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]

/-- Every positive real number is the archimedean norm of an archimedean idele. -/
lemma exists_infiniteUnits_norm_eq (t : ℝ) (ht : 0 < t) :
    ∃ a : (InfiniteAdeleRing F)ˣ,
      ∏ w : InfinitePlace F, ‖(a : InfiniteAdeleRing F) w‖ ^ w.mult = t := by
  classical
  let w₀ : InfinitePlace F := Classical.arbitrary _
  have hm : (0 : ℝ) < (w₀.mult : ℝ) := by
    have := InfinitePlace.mult_pos (w := w₀)
    exact_mod_cast this
  obtain ⟨z, hz⟩ := exists_norm_eq w₀ (t ^ (1 / (w₀.mult : ℝ))) (Real.rpow_pos_of_pos ht _)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact (Real.rpow_pos_of_pos ht (1 / (w₀.mult : ℝ))).ne' hz.symm
  let u : (w : InfinitePlace F) → (w.Completion)ˣ := Pi.mulSingle w₀ (Units.mk0 z hz0)
  let a : (InfiniteAdeleRing F)ˣ :=
    { val := fun w => ((u w : (w.Completion)ˣ) : w.Completion)
      inv := fun w => (((u w)⁻¹ : (w.Completion)ˣ) : w.Completion)
      val_inv := funext fun w => (u w).mul_inv
      inv_val := funext fun w => (u w).inv_mul }
  refine ⟨a, ?_⟩
  have hval : ∀ w, ((a : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w =
      ((u w : (w.Completion)ˣ) : w.Completion) := fun w => rfl
  simp_rw [hval]
  rw [Finset.prod_eq_single w₀]
  · simp only [u, Pi.mulSingle_eq_same, Units.val_mk0]
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, one_div, inv_mul_cancel₀ hm.ne',
      Real.rpow_one]
  · intro w _ hw
    simp only [u, Pi.mulSingle_eq_of_ne hw, Units.val_one, norm_one, one_pow]
  · intro h
    exact absurd (Finset.mem_univ w₀) h

/-- The idele with archimedean part `a` and finite part `x`. -/
noncomputable def mkIdele (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    IdeleGroup F :=
  (Homeomorph.prodUnits : (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)ˣ ≃ₜ _).symm (a, x)

lemma mkIdele_fst (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((mkIdele a x : IdeleGroup F) : AdeleRing (𝓞 F) F).1 = (a : InfiniteAdeleRing F) := rfl

lemma mkIdele_snd (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((mkIdele a x : IdeleGroup F) : AdeleRing (𝓞 F) F).2 = (x : FiniteAdeleRing (𝓞 F) F) := rfl

lemma finPart_mkIdele (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finPart (mkIdele a x) = x := Units.ext rfl

lemma ideleNorm_mkIdele (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ideleNorm (mkIdele a x) = (∏ w : InfinitePlace F, ‖(a : InfiniteAdeleRing F) w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ := rfl

/-- The ideal class of an idele is the class of the content of its finite part, for a
surjective content homomorphism `φ`. -/
theorem exists_contentHom (F : Type*) [Field F] [NumberField F] :
    ∃ φ : (FiniteAdeleRing (𝓞 F) F)ˣ →* (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      (∀ g : IdeleGroup F, ideleIdealClass F g = ClassGroup.mk F (φ (finPart g))) ∧
      Function.Surjective φ := by
  obtain ⟨φ, hφ, -, hsurj, -, -⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
      (𝓞 F) F
  refine ⟨φ, ?_, hsurj⟩
  intro g
  let n : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    -WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v))
  let P : HeightOneSpectrum (𝓞 F) → (Ideal (𝓞 F))⁰ := fun v =>
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (FractionalIdeal.mk0 F (P v)) ^ n v).Finite := by
    refine (finite_valued_ne_one g).subset ?_
    intro v hv h
    apply hv
    change (FractionalIdeal.mk0 F (P v)) ^
      (-WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v))) = 1
    rw [h, WithZero.log_one, neg_zero, zpow_zero]
  have hu : φ (finPart g) = ∏ᶠ v, (FractionalIdeal.mk0 F (P v)) ^ n v := by
    apply Units.ext
    rw [hφ (finPart g)]
    have h1 := MonoidHom.map_finprod_of_injective (Units.coeHom (FractionalIdeal (𝓞 F)⁰ F))
      (fun _ _ h => Units.ext h) (fun v => (FractionalIdeal.mk0 F (P v)) ^ n v)
    rw [Units.coeHom_apply] at h1
    rw [h1]
    refine finprod_congr fun v => ?_
    rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, FractionalIdeal.coe_mk0]
    rfl
  rw [hu, MonoidHom.map_finprod _ hfin]
  unfold ideleIdealClass
  refine finprod_congr fun v => ?_
  rw [map_zpow, ClassGroup.mk_mk0]

/-- The idele `1` has norm `1`. -/
lemma ideleNorm_one : ideleNorm (1 : IdeleGroup F) = 1 := by
  have h := ideleNorm_mul (1 : IdeleGroup F) 1
  rw [one_mul] at h
  have h0 := (ideleNorm_pos (1 : IdeleGroup F)).ne'
  have h2 : ideleNorm (1 : IdeleGroup F) * 1 =
      ideleNorm (1 : IdeleGroup F) * ideleNorm (1 : IdeleGroup F) := by rw [mul_one]; exact h
  exact (mul_left_cancel₀ h0 h2).symm

/-- **Norm-one representatives of the ideal classes**: there is a map `r` from the class group
to the norm-one ideles with `r 1 = 1` and such that `r c` has ideal class `c`. -/
theorem exists_classRep :
    ∃ r : ClassGroup (𝓞 F) → IdeleGroup F, r 1 = 1 ∧ (∀ c, ideleNorm (r c) = 1) ∧
      ∀ c, ideleIdealClass F (r c) = c := by
  classical
  obtain ⟨φ, hcls, hsurj⟩ := exists_contentHom F
  have hrep : ∀ c : ClassGroup (𝓞 F), ∃ g : IdeleGroup F, ideleNorm g = 1 ∧
      ideleIdealClass F g = c := by
    intro c
    obtain ⟨I, hI⟩ : ∃ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ClassGroup.mk F I = c :=
      ClassGroup.induction (R := 𝓞 F) (P := fun c => ∃ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ,
        ClassGroup.mk F I = c) F (fun I => ⟨I, rfl⟩) c
    obtain ⟨x, hx⟩ := hsurj I
    have hpos : 0 < ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ := by
      have h := ideleNorm_pos (mkIdele 1 x)
      rw [ideleNorm_mkIdele] at h
      have h1 : (∏ w : InfinitePlace F,
          ‖((1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ ^ w.mult) = 1 := by
        refine Finset.prod_eq_one fun w _ => ?_
        have : ((1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w = 1 := rfl
        rw [this, norm_one, one_pow]
      rw [h1, one_mul] at h
      exact h
    obtain ⟨a, ha⟩ := exists_infiniteUnits_norm_eq (F := F)
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖)⁻¹ (inv_pos.mpr hpos)
    refine ⟨mkIdele a x, ?_, ?_⟩
    · rw [ideleNorm_mkIdele, ha, inv_mul_cancel₀ hpos.ne']
    · rw [hcls, finPart_mkIdele, hx, hI]
  choose r₀ hr₀n hr₀ using hrep
  refine ⟨fun c => if c = 1 then 1 else r₀ c, by simp, fun c => ?_, fun c => ?_⟩
  · by_cases hc : c = 1
    · simp only [hc, if_true]
      exact ideleNorm_one
    · simp only [hc, if_false]
      exact hr₀n c
  · by_cases hc : c = 1
    · simp only [hc, if_true]
      rw [hcls, map_one, map_one, map_one]
    · simp only [hc, if_false]
      exact hr₀ c

end Sol_MasulloGRH_exists_fundamentalDomain_normOneIdeles

open MasulloGRH Sol_MasulloGRH_exists_fundamentalDomain_normOneIdeles

theorem solution (F : Type*) [Field F] [NumberField F] :
    ∃ E : Set {g : IdeleGroup F // ideleNorm g = 1},
      IsCompact (closure E) ∧ (interior E).Nonempty ∧
      (∀ g : {g : IdeleGroup F // ideleNorm g = 1},
        ∃! ξ : Fˣ, ∃ e ∈ E, (g : IdeleGroup F) = principalIdele F ξ * (e : IdeleGroup F)) ∧
      ∀ K : Set {g : IdeleGroup F // ideleNorm g = 1}, IsCompact K →
        {ξ : Fˣ | ∃ e ∈ closure E, ∃ k ∈ K,
          (k : IdeleGroup F) = principalIdele F ξ * (e : IdeleGroup F)}.Finite := by
  obtain ⟨r, hr₁, hrn, hr⟩ := exists_classRep (F := F)
  let b := Units.basisModTorsion F
  let v₀ : InfinitePlace F := Classical.arbitrary _
  let σ : ℂ ≃ₐ[ℝ] ℂ := AlgEquiv.refl
  obtain ⟨hsub, hE, hint⟩ :=
    tateIdeleDomain_relCompact_and_interior_nonempty F b v₀ σ r hr₁ hrn hr
  refine ⟨{g | g.val ∈ tateIdeleDomain F b v₀ σ r}, hE, hint, ?_, ?_⟩
  · intro g
    obtain ⟨ξ, ⟨e, he, hge⟩, huniq⟩ :=
      tateIdeleDomain_existsUnique_principal_mul F b v₀ σ r hr₁ hrn hr g.val g.property
    refine ⟨ξ, ⟨⟨e, hsub he⟩, he, hge⟩, ?_⟩
    rintro η ⟨e', he', hge'⟩
    exact huniq η ⟨e'.val, he', hge'⟩
  · intro K hK
    -- the set of quotients `K · (closure E)⁻¹` in the idele group is compact
    have hc : Continuous (fun p : {g : IdeleGroup F // ideleNorm g = 1} ×
        {g : IdeleGroup F // ideleNorm g = 1} ↦ (p.1 : IdeleGroup F) * (p.2 : IdeleGroup F)⁻¹) :=
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd).inv
    have hQ := (hK.prod hE).image hc
    refine (finite_principal_mem_of_isCompact _ hQ).subset ?_
    rintro ξ ⟨e, he, k, hk, hke⟩
    exact ⟨(k, e), ⟨hk, he⟩, by
      change (k : IdeleGroup F) * (e : IdeleGroup F)⁻¹ = principalIdele F ξ
      rw [hke, mul_inv_cancel_right]⟩
