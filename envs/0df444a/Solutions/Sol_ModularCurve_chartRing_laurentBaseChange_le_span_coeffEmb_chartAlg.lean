-- Prove2me | solution 1 for ModularCurve.chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c272e55e-2e4a-5857-bd32-a755833be4b9

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg

open ModularCurve AlgebraicCurve
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace CC2B01K1R1

variable {k kb F Fb : Type} [Field k] [Field kb] [Field F] [Field Fb]
  [Algebra k kb] [Algebra kb Fb] [Algebra k F]

private theorem exists_algHom_extends [IsAlgClosed kb] [Algebra.IsAlgebraic k kb]
    (K : IntermediateField k kb) (σ : K →ₐ[k] kb) :
    ∃ σh : kb →ₐ[k] kb, ∀ x : K, σh (x : kb) = σ x := by
  haveI hnorm : Normal k kb := normal_iff.mpr fun x =>
    ⟨(Algebra.IsAlgebraic.isAlgebraic x).isIntegral, IsAlgClosed.splits _⟩
  refine ⟨σ.liftNormal kb, fun x => ?_⟩
  have h := AlgHom.liftNormal_commutes σ kb x
  simpa using h

omit [Algebra k F] in

private theorem isIntegral_map_of_fix (ρ : F →+* Fb) (S : Set F) (σ : kb →ₐ[k] kb) (e : Fb →+* Fb)
    (hec : ∀ c : kb, e (algebraMap kb Fb c) = algebraMap kb Fb (σ c))
    (hef : ∀ f : F, e (ρ f) = ρ f) {y : Fb}
    (hy : IsIntegral (Algebra.adjoin kb (⇑ρ '' S)) y) :
    IsIntegral (Algebra.adjoin kb (⇑ρ '' S)) (e y) := by
  have hmaps : ∀ x, x ∈ Algebra.adjoin kb (⇑ρ '' S) → e x ∈ Algebra.adjoin kb (⇑ρ '' S) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem z hz =>
        obtain ⟨f, hf, rfl⟩ := hz
        rw [hef]
        exact Algebra.subset_adjoin ⟨f, hf, rfl⟩
    | algebraMap c =>
        rw [hec]
        exact Subalgebra.algebraMap_mem _ _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let e' : Algebra.adjoin kb (⇑ρ '' S) →+* Algebra.adjoin kb (⇑ρ '' S) :=
    (e.comp (Algebra.adjoin kb (⇑ρ '' S)).val.toRingHom).codRestrict
      (Algebra.adjoin kb (⇑ρ '' S)) (fun x => hmaps _ x.2)
  exact hy.map_of_comp_eq e' e (by ext a; rfl)

private theorem closure_mem_adjoin (S : Set F) {x : F} (hx : x ∈ Submonoid.closure S) :
    x ∈ Algebra.adjoin k S := by
  induction hx using Submonoid.closure_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | one => exact one_mem _
  | mul a b _ _ ha hb => exact mul_mem ha hb

private theorem isIntegral_of_mem {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    (A : Subalgebra R B) {x : B} (hx : x ∈ A) : IsIntegral A x := by
  simpa using isIntegral_algebraMap (A := B) (x := (⟨x, hx⟩ : A))

private theorem sum_embeddings_smul [CharZero k] [IsAlgClosed kb]
    (K' : IntermediateField k kb) [FiniteDimensional k K'] (w : K') (x : Fb) :
    ∑ σ : K' →ₐ[k] kb, (σ w) • x = (algebraMap k kb (Algebra.trace k K' w)) • x := by
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic k K' := Algebra.IsAlgebraic.of_finite k K'
  haveI : Algebra.IsSeparable k K' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [← Finset.sum_smul]
  rw [show (∑ σ : K' →ₐ[k] kb, σ w) = algebraMap k kb (Algebra.trace k K' w) from
    (trace_eq_sum_embeddings (E := kb)).symm]

omit [Algebra k F] in

private theorem e_apply_rep (ρ : F →+* Fb) {K' : IntermediateField k kb}
    (σ : K' →ₐ[k] kb) (σh : kb →ₐ[k] kb) (hσh : ∀ x : K', σh (x : kb) = σ x)
    (e : Fb →+* Fb) (hec : ∀ c : kb, e (algebraMap kb Fb c) = algebraMap kb Fb (σh c))
    (hef : ∀ f : F, e (ρ f) = ρ f)
    {m : ℕ} (c : Fin m → kb) (hc : ∀ i, c i ∈ K') (g : Fin m → F) :
    e (∑ i, c i • ρ (g i)) = ∑ i, (σ ⟨c i, hc i⟩) • ρ (g i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, hec, hef, ← Algebra.smul_def]
  rw [show σh (c i) = σ ⟨c i, hc i⟩ from hσh ⟨c i, hc i⟩]

private theorem rho_smul (ρ : F →+* Fb)
    (hρ : ∀ q : k, ρ (algebraMap k F q) = algebraMap kb Fb (algebraMap k kb q))
    (q : k) (x : F) : ρ (q • x) = (algebraMap k kb q) • ρ x := by
  rw [Algebra.smul_def, map_mul, hρ, Algebra.smul_def]

private theorem dual_expansion {E : Type} [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k E) (x : E) :
    ∑ t, Algebra.trace k E
      (((Algebra.traceForm k E).dualBasis (traceForm_nondegenerate k E) b t) * x) • b t
      = x := by
  have hco : ∀ t, Algebra.trace k E
      (((Algebra.traceForm k E).dualBasis (traceForm_nondegenerate k E) b t) * x)
      = b.repr x t := by
    intro t
    conv_lhs => rw [← Algebra.traceForm_apply, show x = ∑ s, b.repr x s • b s from
      (b.sum_repr x).symm]
    rw [map_sum]
    rw [Finset.sum_congr rfl fun s _ => ((Algebra.traceForm k E) _).map_smul (b.repr x s) (b s)]
    rw [Finset.sum_congr rfl fun s _ => by
      rw [LinearMap.BilinForm.apply_dualBasis_left]]
    simp [Finset.sum_ite_eq', smul_eq_mul]
  rw [Finset.sum_congr rfl fun t _ => by rw [hco t]]
  exact b.sum_repr x

private theorem isIntegral_of_isIntegral_map [CharZero k] [IsAlgClosed kb] [Algebra.IsAlgebraic k kb]
    (ρ : F →+* Fb) (S : Set F)
    (hρ : ∀ q : k, ρ (algebraMap k F q) = algebraMap kb Fb (algebraMap k kb q))
    (hext : ∀ σh : kb →ₐ[k] kb, ∃ e : Fb →+* Fb,
      (∀ c : kb, e (algebraMap kb Fb c) = algebraMap kb Fb (σh c)) ∧ ∀ f : F, e (ρ f) = ρ f)
    (f : F) (hf : IsIntegral (Algebra.adjoin kb (⇑ρ '' S)) (ρ f)) :
    IsIntegral (Algebra.adjoin k S) f := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  obtain ⟨p, hpm, hpe⟩ := hf
  set P : Polynomial Fb := p.map (algebraMap (Algebra.adjoin kb (⇑ρ '' S)) Fb) with hP
  have hPm : P.Monic := hpm.map _
  have hPe : P.eval (ρ f) = 0 := by
    rw [hP, Polynomial.eval_map]
    exact hpe
  set n := P.natDegree with hn
  have hcoeff : ∀ j, P.coeff j ∈ Submodule.span kb (⇑ρ '' (Submonoid.closure S : Set F)) := by
    intro j
    have h1 : P.coeff j ∈ Algebra.adjoin kb (⇑ρ '' S) := by
      rw [hP, Polynomial.coeff_map]
      exact (p.coeff j).2
    have h2 := Algebra.adjoin_eq_span kb (⇑ρ '' S)
    have h3 : (Submonoid.closure (⇑ρ '' S) : Set Fb) = ⇑ρ '' (Submonoid.closure S : Set F) := by
      rw [← MonoidHom.map_mclosure]
      rfl
    rw [← h3, ← h2]
    exact (Subalgebra.mem_toSubmodule (Algebra.adjoin kb (⇑ρ '' S))).mpr h1
  have hrep : ∀ j, ∃ (m : ℕ) (c : Fin m → kb) (g : Fin m → F),
      (∀ i, g i ∈ Submonoid.closure S) ∧ P.coeff j = ∑ i, c i • ρ (g i) := by
    intro j
    have h := hcoeff j
    rw [Submodule.mem_span_set'] at h
    obtain ⟨m, c, w, hw⟩ := h
    choose g hg hgeq using fun i => (w i).2
    refine ⟨m, c, g, hg, ?_⟩
    rw [← hw]
    exact Finset.sum_congr rfl fun i _ => by rw [hgeq i]
  choose M c g hgmem hceq using hrep
  set T : Set kb := ⋃ j ∈ Finset.range (n + 1), Set.range (c j)
  have hTfin : T.Finite :=
    (Finset.range (n + 1)).finite_toSet.biUnion fun j _ => Set.finite_range (c j)
  set K' : IntermediateField k kb := IntermediateField.adjoin k T
  haveI := hTfin.to_subtype
  haveI hfd : FiniteDimensional k K' := IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hcK' : ∀ j, j < n + 1 → ∀ i, c j i ∈ K' := by
    intro j hj i
    apply IntermediateField.subset_adjoin
    exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj, Set.mem_range_self i⟩
  haveI : Nonempty (K' →ₐ[k] kb) := ⟨K'.val⟩
  set D := Fintype.card (K' →ₐ[k] kb) with hD
  have hD0 : D ≠ 0 := Fintype.card_ne_zero
  choose σh hσh using fun σ : K' →ₐ[k] kb => exists_algHom_extends K' σ
  choose e he1 he2 using fun σ : K' →ₐ[k] kb => hext (σh σ)
  have key : ∀ j, j < n → ∃ r : F, r ∈ Algebra.adjoin k S ∧
      (∑ σ : K' →ₐ[k] kb, e σ (P.coeff j)) = ρ r := by
    intro j hj
    have hj' : j < n + 1 := Nat.lt_succ_of_lt hj
    refine ⟨∑ i, Algebra.trace k K' ⟨c j i, hcK' j hj' i⟩ • g j i, ?_, ?_⟩
    · exact Subalgebra.sum_mem _ fun i _ =>
        Subalgebra.smul_mem _ (closure_mem_adjoin S (hgmem j i)) _
    · calc ∑ σ : K' →ₐ[k] kb, e σ (P.coeff j)
          = ∑ σ : K' →ₐ[k] kb, ∑ i, (σ ⟨c j i, hcK' j hj' i⟩) • ρ (g j i) := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [hceq j]
            exact e_apply_rep ρ σ (σh σ) (hσh σ) (e σ) (he1 σ) (he2 σ) (c j)
              (fun i => hcK' j hj' i) (g j)
        _ = ∑ i, ∑ σ : K' →ₐ[k] kb, (σ ⟨c j i, hcK' j hj' i⟩) • ρ (g j i) := Finset.sum_comm
        _ = ∑ i, (algebraMap k kb (Algebra.trace k K' ⟨c j i, hcK' j hj' i⟩)) • ρ (g j i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact sum_embeddings_smul K' _ _
        _ = ρ (∑ i, Algebra.trace k K' ⟨c j i, hcK' j hj' i⟩ • g j i) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => (rho_smul ρ hρ _ _).symm
  have keyn : (∑ σ : K' →ₐ[k] kb, e σ (P.coeff n)) = (D : Fb) := by
    have h1 : P.coeff n = 1 := by rw [hn]; exact hPm.coeff_natDegree
    rw [h1]
    simp [hD, map_one]
  have heqb : (D : Fb) * (ρ f) ^ n +
      ∑ j ∈ Finset.range n, (∑ σ : K' →ₐ[k] kb, e σ (P.coeff j)) * (ρ f) ^ j = 0 := by
    have h1 : ∑ σ : K' →ₐ[k] kb, e σ (P.eval (ρ f)) = 0 := by
      simp [hPe]
    calc (D : Fb) * (ρ f) ^ n +
        ∑ j ∈ Finset.range n, (∑ σ : K' →ₐ[k] kb, e σ (P.coeff j)) * (ρ f) ^ j
        = ∑ j ∈ Finset.range (n + 1), (∑ σ : K' →ₐ[k] kb, e σ (P.coeff j)) * (ρ f) ^ j := by
          rw [Finset.sum_range_succ, keyn]
          ring
      _ = ∑ σ : K' →ₐ[k] kb, ∑ j ∈ Finset.range (n + 1), e σ (P.coeff j) * (ρ f) ^ j := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
      _ = ∑ σ : K' →ₐ[k] kb, e σ (∑ j ∈ Finset.range (n + 1), P.coeff j * (ρ f) ^ j) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, map_pow, he2]
      _ = ∑ σ : K' →ₐ[k] kb, e σ (P.eval (ρ f)) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          congr 1
          exact (Polynomial.eval_eq_sum_range _).symm
      _ = 0 := h1
  choose r hr1 hr2 using key
  set R : ℕ → F := fun j => if h : j < n then r j h else 0 with hR
  have hRmem : ∀ j, R j ∈ Algebra.adjoin k S := by
    intro j
    simp only [hR]
    by_cases h : j < n
    · rw [dif_pos h]; exact hr1 j h
    · rw [dif_neg h]; exact zero_mem _
  have hReq : ∀ j, j < n → (∑ σ : K' →ₐ[k] kb, e σ (P.coeff j)) = ρ (R j) := by
    intro j h
    simp only [hR]
    rw [dif_pos h]
    exact hr2 j h
  have heqF : ρ ((D : F) * f ^ n + ∑ j ∈ Finset.range n, R j * f ^ j) = 0 := by
    rw [map_add, map_mul, map_pow, map_natCast, map_sum]
    rw [Finset.sum_congr rfl fun j hj => by
      rw [map_mul, map_pow, ← hReq j (Finset.mem_range.mp hj)]]
    exact heqb
  have heqF' : (D : F) * f ^ n + ∑ j ∈ Finset.range n, R j * f ^ j = 0 := by
    apply ρ.injective
    rw [heqF, map_zero]
  rcases Nat.eq_zero_or_pos n with hn0 | _hnpos
  · exfalso
    rw [hn0] at heqF'
    simp at heqF'
    exact hD0 (Nat.cast_eq_zero.mp heqF')
  · have hmem' : ∀ j, (D : k)⁻¹ • R j ∈ Algebra.adjoin k S :=
      fun j => Subalgebra.smul_mem _ (hRmem j) _
    set q : Polynomial (Algebra.adjoin k S) :=
      Polynomial.X ^ n + ∑ j ∈ Finset.range n,
        Polynomial.C (⟨(D : k)⁻¹ • R j, hmem' j⟩ : Algebra.adjoin k S) * Polynomial.X ^ j
      with hq
    have hds : (∑ j ∈ Finset.range n, Polynomial.C
        (⟨(D : k)⁻¹ • R j, hmem' j⟩ : Algebra.adjoin k S) * Polynomial.X ^ j).degree
        < (n : WithBot ℕ) := by
      apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
      rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
      intro j hj
      apply lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
      exact_mod_cast Finset.mem_range.mp hj
    have hqm : q.Monic := by
      rw [hq]
      refine (Polynomial.monic_X_pow n).add_of_left ?_
      rw [Polynomial.degree_X_pow]
      exact hds
    have hqe : Polynomial.eval₂ (algebraMap (Algebra.adjoin k S) F) f q = 0 := by
      rw [hq, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
      rw [Finset.sum_congr rfl fun j (hj : j ∈ Finset.range n) => by
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]]
      have hsc := congrArg (fun z => (algebraMap k F (D : k)⁻¹) * z) heqF'
      simp only [mul_add, mul_zero, Finset.mul_sum] at hsc
      have hlead : (algebraMap k F (D : k)⁻¹) * ((D : F) * f ^ n) = f ^ n := by
        rw [show ((D : F)) = algebraMap k F ((D : k)) from (map_natCast (algebraMap k F) D).symm]
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hD0), map_one, one_mul]
      have hterm : ∀ j, (algebraMap k F (D : k)⁻¹) * (R j * f ^ j)
          = (algebraMap (Algebra.adjoin k S) F
              (⟨(D : k)⁻¹ • R j, hmem' j⟩ : Algebra.adjoin k S)) * f ^ j := by
        intro j
        rw [show (algebraMap (Algebra.adjoin k S) F
            (⟨(D : k)⁻¹ • R j, hmem' j⟩ : Algebra.adjoin k S)) = (D : k)⁻¹ • R j from rfl]
        rw [Algebra.smul_def]
        ring
      rw [hlead] at hsc
      rw [Finset.sum_congr rfl fun j _ => hterm j] at hsc
      exact hsc
    exact ⟨q, hqm, hqe⟩

private theorem mem_span_image_integral [CharZero k] [IsAlgClosed kb] [Algebra.IsAlgebraic k kb]
    (ρ : F →+* Fb) (S : Set F)
    (hρ : ∀ q : k, ρ (algebraMap k F q) = algebraMap kb Fb (algebraMap k kb q))
    (hext : ∀ σh : kb →ₐ[k] kb, ∃ e : Fb →+* Fb,
      (∀ c : kb, e (algebraMap kb Fb c) = algebraMap kb Fb (σh c)) ∧ ∀ f : F, e (ρ f) = ρ f)
    (hspan : ∀ y : Fb, y ∈ Submodule.span kb (Set.range ⇑ρ))
    {y : Fb} (hy : IsIntegral (Algebra.adjoin kb (⇑ρ '' S)) y) :
    y ∈ Submodule.span kb (⇑ρ '' {f : F | IsIntegral (Algebra.adjoin k S) f}) := by
  classical
  have h := hspan y
  rw [Submodule.mem_span_set'] at h
  obtain ⟨m, cc, w, hw⟩ := h
  choose g hgeq using fun i => (w i).2
  have hy_rep : y = ∑ i, cc i • ρ (g i) := by
    rw [← hw]
    exact Finset.sum_congr rfl fun i _ => by rw [hgeq i]
  set T : Set kb := Set.range cc
  have hTfin : T.Finite := Set.finite_range cc
  set K' : IntermediateField k kb := IntermediateField.adjoin k T
  haveI := hTfin.to_subtype
  haveI hfd : FiniteDimensional k K' := IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic k K' := Algebra.IsAlgebraic.of_finite k K'
  haveI : Algebra.IsSeparable k K' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hcK' : ∀ i, cc i ∈ K' := fun i =>
    IntermediateField.subset_adjoin k T (Set.mem_range_self i)
  set u : Module.Basis (Fin (Module.finrank k K')) k K' := Module.finBasis k K'
  set a : Module.Basis (Fin (Module.finrank k K')) k K' :=
    (Algebra.traceForm k K').dualBasis (traceForm_nondegenerate k K') u
  haveI : Nonempty (K' →ₐ[k] kb) := ⟨K'.val⟩
  choose σh hσh using fun σ : K' →ₐ[k] kb => exists_algHom_extends K' σ
  choose e he1 he2 using fun σ : K' →ₐ[k] kb => hext (σh σ)
  set ft : Fin (Module.finrank k K') → F := fun t =>
    ∑ i, Algebra.trace k K' (a t * ⟨cc i, hcK' i⟩) • g i with hft
  have hB : ∀ t, ρ (ft t) = ∑ σ : K' →ₐ[k] kb, (σ (a t)) • e σ y := by
    intro t
    have h1 : ∀ σ : K' →ₐ[k] kb, e σ y = ∑ i, (σ ⟨cc i, hcK' i⟩) • ρ (g i) := fun σ => by
      rw [hy_rep]
      exact e_apply_rep ρ σ (σh σ) (hσh σ) (e σ) (he1 σ) (he2 σ) cc hcK' g
    calc ρ (ft t)
        = ∑ i, (algebraMap k kb (Algebra.trace k K' (a t * ⟨cc i, hcK' i⟩))) • ρ (g i) := by
          rw [hft, map_sum]
          exact Finset.sum_congr rfl fun i _ => rho_smul ρ hρ _ _
      _ = ∑ i, ∑ σ : K' →ₐ[k] kb, (σ (a t * ⟨cc i, hcK' i⟩)) • ρ (g i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (sum_embeddings_smul K' _ _).symm
      _ = ∑ σ : K' →ₐ[k] kb, ∑ i, ((σ (a t)) * (σ ⟨cc i, hcK' i⟩)) • ρ (g i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => by
            rw [map_mul]
      _ = ∑ σ : K' →ₐ[k] kb, (σ (a t)) • e σ y := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [h1 σ, Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => (smul_smul _ _ _).symm
  have hint : ∀ t, IsIntegral (Algebra.adjoin kb (⇑ρ '' S)) (ρ (ft t)) := by
    intro t
    rw [hB t]
    have hterm : ∀ σ : K' →ₐ[k] kb,
        (σ (a t)) • e σ y ∈ integralClosure (Algebra.adjoin kb (⇑ρ '' S)) Fb := by
      intro σ
      rw [Algebra.smul_def]
      exact mul_mem
        (isIntegral_of_mem _ (Subalgebra.algebraMap_mem (Algebra.adjoin kb (⇑ρ '' S)) (σ (a t))))
        (isIntegral_map_of_fix ρ S (σh σ) (e σ) (he1 σ) (he2 σ) hy)
    exact sum_mem fun σ _ => hterm σ
  have hA : y = ∑ t, ((u t : kb)) • ρ (ft t) := by
    calc y = ∑ i, cc i • ρ (g i) := hy_rep
      _ = ∑ i, (((⟨cc i, hcK' i⟩ : K') : kb)) • ρ (g i) := rfl
      _ = ∑ i, ((((∑ t, Algebra.trace k K' (a t * ⟨cc i, hcK' i⟩) • u t : K')) : kb)) •
            ρ (g i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show ((⟨cc i, hcK' i⟩ : K') : kb)
            = ((∑ t, Algebra.trace k K' (a t * ⟨cc i, hcK' i⟩) • u t : K') : kb) from
            congrArg (fun z : K' => (z : kb)) (dual_expansion u ⟨cc i, hcK' i⟩).symm]
      _ = ∑ i, ∑ t, ((u t : kb)) •
            (algebraMap k kb (Algebra.trace k K' (a t * ⟨cc i, hcK' i⟩))) • ρ (g i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show ((((∑ t, Algebra.trace k K' (a t * ⟨cc i, hcK' i⟩) • u t : K')) : kb))
            = ∑ t, (algebraMap k kb (Algebra.trace k K' (a t * ⟨cc i, hcK' i⟩))) * ((u t : kb))
            by
              rw [AddSubmonoidClass.coe_finsetSum]
              exact Finset.sum_congr rfl fun t _ => by
                rw [SetLike.val_smul, Algebra.smul_def]]
          rw [Finset.sum_smul]
          exact Finset.sum_congr rfl fun t _ => by rw [mul_comm, mul_smul]
      _ = ∑ t, ((u t : kb)) •
            ∑ i, (algebraMap k kb (Algebra.trace k K' (a t * ⟨cc i, hcK' i⟩))) • ρ (g i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          exact (Finset.smul_sum).symm
      _ = ∑ t, ((u t : kb)) • ρ (ft t) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          congr 1
          rw [hft, map_sum]
          exact (Finset.sum_congr rfl fun i _ => rho_smul ρ hρ _ _).symm
  rw [hA]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span
    ⟨ft t, isIntegral_of_isIntegral_map ρ S hρ hext (ft t) (hint t), rfl⟩

end CC2B01K1R1

namespace CC2B01K1R2

open Polynomial

section Localisation

variable {Z k E : Type} [CommRing Z] [Field k] [CommRing E] [Algebra Z k] [Algebra k E]
  [Algebra Z E] [IsScalarTower Z k E]

private theorem exists_natCast_mul_mem_adjoin
    (hden : ∀ a : k, ∃ n : ℕ, n ≠ 0 ∧ ∃ z : Z, algebraMap Z k z = (n : k) * a)
    (S : Set E) {a : E} (ha : a ∈ Algebra.adjoin k S) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : E) * a ∈ Algebra.adjoin Z S := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    exact ⟨1, one_ne_zero, by rw [Nat.cast_one, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap c =>
    obtain ⟨n, hn, z, hz⟩ := hden c
    refine ⟨n, hn, ?_⟩
    have h : (n : E) * algebraMap k E c = algebraMap Z E z := by
      rw [IsScalarTower.algebraMap_apply Z k E, hz, map_mul, map_natCast]
    rw [h]
    exact Subalgebra.algebraMap_mem _ z
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hym⟩ := hy
    obtain ⟨n, hn, hzn⟩ := hz
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have h : ((m * n : ℕ) : E) * (y + z) = (n : E) * ((m : E) * y) + (m : E) * ((n : E) * z) := by
      push_cast; ring
    rw [h]
    exact add_mem (mul_mem (natCast_mem _ n) hym) (mul_mem (natCast_mem _ m) hzn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm, hym⟩ := hy
    obtain ⟨n, hn, hzn⟩ := hz
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have h : ((m * n : ℕ) : E) * (y * z) = ((m : E) * y) * ((n : E) * z) := by
      push_cast; ring
    rw [h]
    exact mul_mem hym hzn

private theorem exists_isIntegral_natCast_mul [Nontrivial E]
    (hden : ∀ a : k, ∃ n : ℕ, n ≠ 0 ∧ ∃ z : Z, algebraMap Z k z = (n : k) * a)
    (S : Set E) {x : E} (hx : IsIntegral (Algebra.adjoin k S) x) :
    ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Algebra.adjoin Z S) ((n : E) * x) := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := hx
  have hcoeff : ∀ i, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * (p.coeff i : E) ∈ Algebra.adjoin Z S :=
    fun i => exists_natCast_mul_mem_adjoin hden S (p.coeff i).2
  choose n hn0 hn using hcoeff
  set M : ℕ := ∏ i ∈ Finset.range (p.natDegree + 1), n i with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hn0 i
  have hMcoeff : ∀ i ≤ p.natDegree, (M : E) * (p.coeff i : E) ∈ Algebra.adjoin Z S := by
    intro i hi
    obtain ⟨c, hc⟩ : n i ∣ M :=
      Finset.dvd_prod_of_mem n (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    rw [hc, Nat.cast_mul, mul_comm (n i : E) (c : E), mul_assoc]
    exact mul_mem (natCast_mem _ c) (hn i)
  set q : E[X] := (p.map (algebraMap (Algebra.adjoin k S) E)).scaleRoots (M : E) with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval ((M : E) * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]
  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin Z S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · have hsplit : p.natDegree - i = (p.natDegree - i - 1) + 1 :=
        (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hi)).symm
      rw [hsplit, pow_succ, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : E) * ((M : E) ^ (p.natDegree - i - 1) * (M : E))
            = (M : E) ^ (p.natDegree - i - 1) * ((M : E) * (p.coeff i : E)) by ring]
      exact mul_mem (pow_mem (natCast_mem _ M) _) (hMcoeff i hi.le)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _
  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Z S) E) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨M, hM0, q', hq'monic, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

private theorem mem_span_isIntegral_adjoin [Nontrivial E] [CharZero k]
    (hden : ∀ a : k, ∃ n : ℕ, n ≠ 0 ∧ ∃ z : Z, algebraMap Z k z = (n : k) * a)
    (S : Set E) {x : E} (hx : IsIntegral (Algebra.adjoin k S) x) :
    x ∈ Submodule.span k {b : E | IsIntegral (Algebra.adjoin Z S) b} := by
  obtain ⟨n, hn0, hint⟩ := exists_isIntegral_natCast_mul hden S hx
  have hn : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hx' : x = (n : k)⁻¹ • ((n : E) * x) := by
    rw [← map_natCast (algebraMap k E) n, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hn,
      one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hint)

end Localisation

section RatLocalized

private theorem hden_ratLocalizedAt (p : ℕ) (a : ℚ) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ z : GaloisRep.ratLocalizedAt p,
      algebraMap (GaloisRep.ratLocalizedAt p) ℚ z = (n : ℚ) * a := by
  refine ⟨a.den, a.den_nz, ⟨(a.num : ℚ), ?_⟩, ?_⟩
  · show ((a.num : ℚ)).den.Coprime p
    simp
  · show ((a.num : ℚ)) = (a.den : ℚ) * a
    rw [mul_comm]
    exact (Rat.mul_den_eq_num a).symm

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ)

private theorem mem_chartAlg_iff' {S : Set ↥F₀}
    {x : ↥F₀} :
    x ∈ TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S ↔ IsIntegral (Algebra.adjoin (GaloisRep.ratLocalizedAt p) S) x :=
  Iff.rfl

private theorem mem_span_chartAlg (S : Set ↥F₀)
    {x : ↥F₀} (hx : IsIntegral (Algebra.adjoin ℚ S) x) :
    x ∈ Submodule.span ℚ (TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S : Set ↥F₀) :=
  mem_span_isIntegral_adjoin (Z := GaloisRep.ratLocalizedAt p) (hden_ratLocalizedAt p) S hx

private theorem exists_int_smul_mem_chartAlg (S : Set ↥F₀)
    {x : ↥F₀} (hx : IsIntegral (Algebra.adjoin ℚ S) x) :
    ∃ d : ℤ, d ≠ 0 ∧ (d : ℚ) • x ∈ TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S := by
  obtain ⟨n, hn0, hint⟩ :=
    exists_isIntegral_natCast_mul (Z := GaloisRep.ratLocalizedAt p) (hden_ratLocalizedAt p) S hx
  refine ⟨n, Int.natCast_ne_zero.mpr hn0, ?_⟩
  have h : ((n : ℤ) : ℚ) • x = (n : ↥F₀) * x := by
    rw [Int.cast_natCast, ← map_natCast (algebraMap ℚ ↥F₀) n,
      ← Algebra.smul_def]
  rw [h]
  exact hint

end RatLocalized

section HSpan

open scoped TensorProduct

private theorem span_range_one_tmul_eq_top (k K E : Type) [Field k] [Field K] [Algebra k K]
    [AddCommGroup E] [Module k E] :
    Submodule.span K (Set.range fun f : E => (1 : K) ⊗ₜ[k] f) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul c f =>
    rw [show c ⊗ₜ[k] f = c • ((1 : K) ⊗ₜ[k] f) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨f, rfl⟩)

private theorem span_range_comp_eq_top {K T V ι : Type} [Field K] [AddCommGroup T] [Module K T]
    [AddCommGroup V] [Module K V] (e : T ≃ₗ[K] V) (v : ι → T)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    Submodule.span K (Set.range (⇑e ∘ v)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : x ∈ Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
  rw [Set.range_comp]
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

private theorem span_range_coeffEmb_eq_top :
    Submodule.span (AlgebraicClosure ℚ)
      (Set.range fun f : ↥F₀ =>
        (⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :
            ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) = ⊤ := by
  have h := span_range_comp_eq_top
    (baseChangeEquiv (AlgebraicClosure ℚ) F₀).toLinearEquiv
    (fun f : ↥F₀ => (1 : AlgebraicClosure ℚ) ⊗ₜ[ℚ] f)
    (span_range_one_tmul_eq_top ℚ (AlgebraicClosure ℚ) ↥F₀)
  have hfun : (⇑(baseChangeEquiv (AlgebraicClosure ℚ) F₀).toLinearEquiv ∘
      fun f : ↥F₀ => (1 : AlgebraicClosure ℚ) ⊗ₜ[ℚ] f) =
      fun f : ↥F₀ =>
        (⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :
            ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) :=
    funext fun f => baseChangeEquiv_one_tmul (AlgebraicClosure ℚ) F₀ f
  rw [hfun] at h
  exact h

private theorem hspan (w : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
    w ∈ Submodule.span (AlgebraicClosure ℚ)
      (Set.range fun f : ↥F₀ =>
        (⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :
            ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) := by
  rw [span_range_coeffEmb_eq_top]
  exact Submodule.mem_top

end HSpan

end CC2B01K1R2

namespace CC2B01K1R3

open scoped TensorProduct

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

private def rho : ↥F₀ →+* ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) where
  toFun f := ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul (coeffEmb (AlgebraicClosure ℚ)) _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add (coeffEmb (AlgebraicClosure ℚ)) _ _)

private theorem coe_rho (f : ↥F₀) :
    ((rho F₀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) := rfl

private theorem rho_eq_baseChangeEquiv_one_tmul (f : ↥F₀) :
    rho F₀ f = baseChangeEquiv (AlgebraicClosure ℚ) F₀ (1 ⊗ₜ f) :=
  (baseChangeEquiv_one_tmul (AlgebraicClosure ℚ) F₀ f).symm

private theorem rho_algebraMap (q : ℚ) :
    rho F₀ (algebraMap ℚ ↥F₀ q) =
      algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)
        (algebraMap ℚ (AlgebraicClosure ℚ) q) :=
  RingHom.congr_fun (Subsingleton.elim
    ((rho F₀).comp (algebraMap ℚ ↥F₀))
    ((algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)).comp
      (algebraMap ℚ (AlgebraicClosure ℚ)))) q

private theorem rho_rat_smul_eq (q : ℚ) (f : ↥F₀) :
    rho F₀ (q • f) = algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)
      (algebraMap ℚ (AlgebraicClosure ℚ) q) * rho F₀ f := by
  rw [Algebra.smul_def, map_mul, rho_algebraMap]

private theorem coeffMap_coeffEmb_endo (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
    (x : LaurentSeries ℚ) :
    coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
        (coeffEmb (AlgebraicClosure ℚ) x) = coeffEmb (AlgebraicClosure ℚ) x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun c => σ.commutes c) x

private theorem coeffMap_endo_mem (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ (laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
    coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x ∈ (laurentBaseChange (AlgebraicClosure ℚ) F₀) := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
    · rw [coeffMap_algebraMap]; exact (laurentBaseChange (AlgebraicClosure ℚ) F₀).algebraMap_mem _
    · rw [coeffMap_coeffEmb_endo]; exact coeffEmb_mem_laurentBaseChange _ hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

private def coeffEndo (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) :
    ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) →+* ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) where
  toFun x := ⟨coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) x, coeffMap_endo_mem F₀ σ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

private theorem hext (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ e : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) →+* ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀),
      (∀ c : AlgebraicClosure ℚ,
        e (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) c) =
          algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) (σ c)) ∧
      ∀ f : ↥F₀, e (rho F₀ f) = rho F₀ f :=
  ⟨coeffEndo F₀ σ,
    fun c => Subtype.ext (coeffMap_algebraMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) c),
    fun f => Subtype.ext (coeffMap_coeffEmb_endo σ (f : LaurentSeries ℚ))⟩

private theorem hspan (y : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
    y ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range ⇑(rho F₀)) := by
  have heq : (fun f : ↥F₀ => rho F₀ f) =
      ⇑(baseChangeEquiv (AlgebraicClosure ℚ) F₀).toLinearEquiv ∘
        (fun f => (1 : AlgebraicClosure ℚ) ⊗ₜ[ℚ] f) :=
    funext fun f => rho_eq_baseChangeEquiv_one_tmul F₀ f
  rw [show ⇑(rho F₀) = (fun f => rho F₀ f) from rfl, heq,
    CC2B01K1R2.span_range_comp_eq_top _ _
      (CC2B01K1R2.span_range_one_tmul_eq_top ℚ (AlgebraicClosure ℚ) ↥F₀)]
  exact Submodule.mem_top

private theorem range_family_eq (p : ℕ) (S : Set ↥F₀) :
    (Set.range fun b : TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S =>
      (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (b : ↥F₀).2⟩ : (laurentBaseChange (AlgebraicClosure ℚ) F₀))) =
    (rho F₀) '' (TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S : Set ↥F₀) := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨b, rfl⟩; exact ⟨(b : ↥F₀), b.2, rfl⟩
  · rintro ⟨f, hf, rfl⟩; exact ⟨⟨f, hf⟩, rfl⟩

private theorem chartRing_le_span_generic (p : ℕ) (S : Set ↥F₀) :
    (AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ((rho F₀) '' S : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ)
        ((rho F₀) '' (TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S : Set ↥F₀)) := by
  intro y hy

  have hint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ((rho F₀) '' S)) y :=
    (AlgebraicCurve.CurveModel.mem_chartRing_iff _).mp hy
  have hR1 := CC2B01K1R1.mem_span_image_integral (k := ℚ) (kb := AlgebraicClosure ℚ)
    (F := ↥F₀) (Fb := ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (rho F₀) S (rho_algebraMap F₀) (hext F₀) (hspan F₀) hint

  refine Submodule.span_le.mpr ?_ hR1
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨d, hd0, hdf⟩ := CC2B01K1R2.exists_int_smul_mem_chartAlg F₀ p S hf
  have hdℚ : (algebraMap ℚ (AlgebraicClosure ℚ) (d : ℚ)) ≠ 0 :=
    fun h => hd0 (Int.cast_eq_zero.mp ((algebraMap ℚ (AlgebraicClosure ℚ)).injective
      (h.trans (map_zero _).symm)))
  have heq : rho F₀ f = algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)
      (algebraMap ℚ (AlgebraicClosure ℚ) (d : ℚ))⁻¹ * rho F₀ ((d : ℚ) • f) := by
    rw [rho_rat_smul_eq, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hdℚ, map_one, one_mul]
  rw [heq, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(d : ℚ) • f, hdf, rfl⟩)

variable {F₀}
variable (j : ↥F₀) (jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
  (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ))
include hjb

private theorem jb_eq_rho : jb = rho F₀ j := Subtype.ext hjb

private theorem singleton_jb_eq :
    ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) = (rho F₀) '' {j} := by
  rw [Set.image_singleton, jb_eq_rho j jb hjb]

private theorem singleton_jb_inv_eq :
    ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) = (rho F₀) '' {j⁻¹} := by
  rw [Set.image_singleton, map_inv₀, jb_eq_rho j jb hjb]

end CC2B01K1R3

theorem solution
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) (j : ↥F₀) [Fact (j ≠ 0)]
    (jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ)) :
    (AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ∧
    (AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) := by
  refine ⟨?_, ?_⟩
  · rw [CC2B01K1R3.range_family_eq F₀ p {j}, CC2B01K1R3.singleton_jb_eq j jb hjb]
    exact CC2B01K1R3.chartRing_le_span_generic F₀ p {j}
  · rw [CC2B01K1R3.range_family_eq F₀ p {j⁻¹}, CC2B01K1R3.singleton_jb_inv_eq j jb hjb]
    exact CC2B01K1R3.chartRing_le_span_generic F₀ p {j⁻¹}

end

end S_ModularCurve_chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg
end P2MW
export P2MW.S_ModularCurve_chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg (solution)
