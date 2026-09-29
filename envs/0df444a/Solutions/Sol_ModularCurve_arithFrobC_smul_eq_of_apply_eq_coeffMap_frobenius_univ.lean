-- Prove2me | solution 1 for ModularCurve.arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a37de5b4-2843-5364-8f00-7b8424dd4b7e

import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_modularFunctionFieldC_algHom_ext
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ

set_option autoImplicit false

noncomputable section

namespace SsfrobRE1Sol

section Kit

variable (q N : ℕ) [NeZero N] {K : Type*} [Field K] [Fact q.Prime] [CharP K q] [PerfectField K]

omit [PerfectField K] in

private theorem coeffMap_injective (τ : K →+* K) (hτ : Function.Injective τ) :
    Function.Injective (ModularCurve.coeffMap (R := K) (S := K) τ) := by
  intro x y hxy
  ext k
  have h := congrArg (fun z : LaurentSeries K => z.coeff k) hxy
  simp only [ModularCurve.coeffMap_coeff] at h
  exact hτ h

omit [PerfectField K] in

private theorem order_coeffMap (τ : K →+* K) (hτ : Function.Injective τ) (x : LaurentSeries K) :
    (ModularCurve.coeffMap τ x).order = x.order := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, HahnSeries.order_zero]
  have hne : ModularCurve.coeffMap τ x ≠ 0 := fun h =>
    hx (coeffMap_injective τ hτ (by rw [h, map_zero]))
  apply le_antisymm
  · refine HahnSeries.order_le_of_coeff_ne_zero ?_
    rw [ModularCurve.coeffMap_coeff]
    intro h0
    exact HahnSeries.coeff_order_eq_zero.not.2 hx (hτ (by rw [h0, map_zero]))
  · rw [HahnSeries.le_order_iff_forall hne]
    intro j hj
    rw [ModularCurve.coeffMap_coeff, HahnSeries.coeff_eq_zero_of_lt_order hj, map_zero]

private theorem coeffMap_symm_coeffMap_frobenius (x : LaurentSeries K) :
    ModularCurve.coeffMap (((frobeniusEquiv K q).symm : K ≃+* K) : K →+* K)
      (ModularCurve.coeffMap (frobenius K q) x) = x := by
  rw [ModularCurve.coeffMap_coeffMap,
    ModularCurve.coeffMap_congr (g := RingHom.id K)
      (RingHom.ext fun a => (frobeniusEquiv K q).symm_apply_apply a) x,
    ModularCurve.coeffMap_id]

private theorem coeffMap_frobenius_coeffMap_symm (x : LaurentSeries K) :
    ModularCurve.coeffMap (frobenius K q)
      (ModularCurve.coeffMap (((frobeniusEquiv K q).symm : K ≃+* K) : K →+* K) x) = x := by
  rw [ModularCurve.coeffMap_coeffMap,
    ModularCurve.coeffMap_congr (g := RingHom.id K)
      (RingHom.ext fun a => (frobeniusEquiv K q).apply_symm_apply a) x,
    ModularCurve.coeffMap_id]

private def frobConj (ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K) :
    ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K where
  toRingHom :=
    (ModularCurve.coeffMap (((frobeniusEquiv K q).symm : K ≃+* K) : K →+* K)).comp
      (ι.toRingHom.comp
        (ModularCurve.coeffRingAut N (frobeniusEquiv K q) : _ ≃+* _).toRingHom)
  commutes' := fun a => by
    show ModularCurve.coeffMap (((frobeniusEquiv K q).symm : K ≃+* K) : K →+* K)
        (ι ((ModularCurve.coeffRingAut N (frobeniusEquiv K q))
          (algebraMap K ↥(ModularCurve.modularFunctionFieldC K N) a)))
      = algebraMap K (LaurentSeries K) a
    rw [ModularCurve.coeffRingAut_algebraMap, AlgHom.commutes,
      ModularCurve.coeffMap_algebraMap,
      show (((frobeniusEquiv K q).symm : K ≃+* K) : K →+* K) ((frobeniusEquiv K q) a)
        = a from (frobeniusEquiv K q).symm_apply_apply a]

private theorem frobConj_apply (ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (z : ↥(ModularCurve.modularFunctionFieldC K N)) :
    frobConj q N ι z
      = ModularCurve.coeffMap (((frobeniusEquiv K q).symm : K ≃+* K) : K →+* K)
          (ι (ModularCurve.coeffRingAut N (frobeniusEquiv K q) z)) :=
  rfl

private theorem frobConj_eq_of_generators
    (ι ι' : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (hj : ι' ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩))
    (hjN : ι' ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩)) :
    frobConj q N ι' = ι := by
  refine ModularCurve.modularFunctionFieldC_algHom_ext K N ?_ ?_
  · rw [frobConj_apply]
    rw [show ModularCurve.coeffRingAut N (frobeniusEquiv K q)
          ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩
        = ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩ from Subtype.ext
          (ModularCurve.coeffSemilinearAut.coeffMap_jqModC
            ((frobeniusEquiv K q : K ≃+* K) : K →+* K))]
    rw [hj, coeffMap_symm_coeffMap_frobenius]
  · rw [frobConj_apply]
    rw [show ModularCurve.coeffRingAut N (frobeniusEquiv K q)
          ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩
        = ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩ from Subtype.ext
          (ModularCurve.coeffSemilinearAut.coeffMap_jqNModC
            ((frobeniusEquiv K q : K ≃+* K) : K →+* K) N)]
    rw [hjN, coeffMap_symm_coeffMap_frobenius]

private theorem apply_coeffRingAut_eq
    (ι ι' : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (hj : ι' ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩))
    (hjN : ι' ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩))
    (z : ↥(ModularCurve.modularFunctionFieldC K N)) :
    ι' (ModularCurve.coeffRingAut N (frobeniusEquiv K q) z)
      = ModularCurve.coeffMap (frobenius K q) (ι z) := by
  have h := congrArg (fun f : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K
      => ModularCurve.coeffMap (frobenius K q) (f z))
    (frobConj_eq_of_generators q N ι ι' hj hjN)
  simp only [frobConj_apply] at h
  rw [coeffMap_frobenius_coeffMap_symm] at h
  exact h

end Kit

end SsfrobRE1Sol

theorem solution
    (q N : ℕ) [NeZero N] (K : Type*) [Field K] [Fact q.Prime] [CharP K q] [PerfectField K]
    (ι ι' : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (hj : ι' ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩))
    (hjN : ι' ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩
      = ModularCurve.coeffMap (frobenius K q)
          (ι ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩))
    (w w' : AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N))
    (hw : ∀ x, x ∈ w.toValuationSubring ↔ 0 ≤ (ι x).order)
    (hw' : ∀ x, x ∈ w'.toValuationSubring ↔ 0 ≤ (ι' x).order) :
    ModularCurve.arithFrobC q K N • w = w' := by
  ext1
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    AlgebraicCurve.SemilinearAut.inv_smul_def]
  rw [hw, hw']
  rw [show AlgebraicCurve.SemilinearAut.toRingAut (ModularCurve.arithFrobC q K N)
      = ModularCurve.coeffRingAut N (frobeniusEquiv K q) from rfl]
  have hint := SsfrobRE1Sol.apply_coeffRingAut_eq q N ι ι' hj hjN
    ((ModularCurve.coeffRingAut N (frobeniusEquiv K q)).symm x)
  rw [RingEquiv.apply_symm_apply] at hint
  rw [show ι' x = ModularCurve.coeffMap (frobenius K q)
        (ι ((ModularCurve.coeffRingAut N (frobeniusEquiv K q)).symm x)) from hint,
    SsfrobRE1Sol.order_coeffMap (frobenius K q) (frobenius K q).injective]

end
end S_ModularCurve_arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ
end P2MW
export P2MW.S_ModularCurve_arithFrobC_smul_eq_of_apply_eq_coeffMap_frobenius_univ (solution)
