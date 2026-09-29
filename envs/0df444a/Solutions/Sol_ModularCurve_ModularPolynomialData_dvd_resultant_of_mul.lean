-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.dvd_resultant_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/38abde86-4571-583d-b549-971fbb4d00b7

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_phiIrreducible_all
import Theorems.Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq
import Theorems.Thm_ModularCurve_transcendental_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve Polynomial IntermediateField

namespace P2MKcResPhi

theorem evalAtJGen_injective : Function.Injective evalAtJGen := by
  intro a b h
  have h' := congrArg (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) h
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, algebraMap_comp_evalAtJGen, evalAtJ_def] at h'

  have hinjQ : Function.Injective (Polynomial.aeval (R := ℚ) jq) :=
    transcendental_iff_injective.1 transcendental_jq
  have key : ∀ c : Polynomial ℤ, (Polynomial.aeval (R := ℤ) jq).toRingHom c =
      Polynomial.aeval (R := ℚ) jq (c.map (Int.castRingHom ℚ)) := by
    intro c
    change Polynomial.aeval (R := ℤ) jq c = _
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  rw [key, key] at h'
  have := hinjQ h'
  exact Polynomial.map_injective (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int this

theorem qExpand_comp_evalAtJ (ℓ : ℕ) [NeZero ℓ] :
    (qExpand ℚ ℓ).comp evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (jqN ℓ) := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

end P2MKcResPhi

open P2MKcResPhi in
theorem solution
    (ℓ M : ℕ) [NeZero ℓ] [NeZero M]
    (dℓ : ModularPolynomialData ℓ) (dM : ModularPolynomialData M)
    (dN : ModularPolynomialData (ℓ * M)) :
    dN.Φ ∣ (dℓ.Φ.map (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ))).resultant
      (dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom (Polynomial (Polynomial ℤ))))
        (Polynomial.C Polynomial.X)) := by

  set B := Polynomial (Polynomial ℤ)
  set f : Polynomial B := dℓ.Φ.map (Polynomial.C : Polynomial ℤ →+* B) with hf
  set g : Polynomial B := dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom B))
    (Polynomial.C Polynomial.X) with hg
  set R : B := f.resultant g with hR
  set L := LaurentSeries ℚ

  set Ξ : B →+* L := Polynomial.eval₂RingHom evalAtJ (jqN (ℓ * M)) with hΞ
  have hΞC : Ξ.comp Polynomial.C = evalAtJ := RingHom.ext fun a => by
    rw [RingHom.comp_apply, hΞ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  have hΞX : Ξ Polynomial.X = jqN (ℓ * M) := by
    rw [hΞ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

  set f' : Polynomial L := dℓ.Φ.map evalAtJ with hf'
  set g' : Polynomial L := dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom L))
    (Polynomial.C (jqN (ℓ * M))) with hg'
  have hff' : f.map Ξ = f' := by
    rw [hf, Polynomial.map_map, hΞC]
  have hgg' : g.map Ξ = g' := by
    rw [hg, ← Polynomial.coe_mapRingHom, Polynomial.hom_eval₂, hg']
    congr 1
    · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp
    · rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hΞX]

  have hfm : f.Monic := dℓ.monic.map _
  have hf'm : f'.Monic := dℓ.monic.map _
  have hdegf : f'.natDegree = f.natDegree := by
    rw [hf', hf, dℓ.monic.natDegree_map, dℓ.monic.natDegree_map]

  set z₀ : L := jqN ℓ with hz₀
  have hfz : f'.eval z₀ = 0 := by
    rw [hf', Polynomial.eval_map]
    exact dℓ.eval_eq_zero
  have hgz : g'.eval z₀ = 0 := by
    rw [hg', ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂, Polynomial.coe_evalRingHom,
      Polynomial.eval_C]
    have h1 : (Polynomial.evalRingHom z₀).comp (Polynomial.mapRingHom (Int.castRingHom L)) =
        Polynomial.eval₂RingHom (Int.castRingHom L) z₀ := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp
    rw [h1, ← qExpand_comp_evalAtJ ℓ]
    have h2 : jqN (ℓ * M) = qExpand ℚ ℓ (jqN M) := by
      rw [jqN, jqN, qExpand_qExpand]
    rw [h2, ← Polynomial.hom_eval₂, dM.eval_eq_zero, map_zero]

  have hRes : f'.resultant g' f.natDegree g.natDegree = 0 := by
    set Lb := AlgebraicClosure L
    apply (algebraMap L Lb).injective
    rw [map_zero, ← Polynomial.resultant_map_map]
    have hsplit : (f'.map (algebraMap L Lb)).Splits := IsAlgClosed.splits _
    have hdeg1 : (f'.map (algebraMap L Lb)).natDegree = f.natDegree := by
      rw [Polynomial.natDegree_map, hdegf]
    have hdeg2 : (g'.map (algebraMap L Lb)).natDegree ≤ g.natDegree := by
      rw [Polynomial.natDegree_map, ← hgg']
      exact Polynomial.natDegree_map_le
    rw [← hdeg1, Polynomial.resultant_eq_prod_eval _ _ _ hdeg2 hsplit]
    have hz : algebraMap L Lb z₀ ∈ (f'.map (algebraMap L Lb)).roots := by
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hf'm.ne_zero), Polynomial.IsRoot.def,
        Polynomial.eval_map, Polynomial.eval₂_hom, hfz, map_zero]
    have hz' : Polynomial.eval (algebraMap L Lb z₀) (g'.map (algebraMap L Lb)) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, hgz, map_zero]
    rw [Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, hz, hz'⟩), mul_zero]
  have hΞR : Ξ R = 0 := by
    rw [hR, ← Polynomial.resultant_map_map, hff', hgg']
    exact hRes

  set θ : B →+* Polynomial ℚ⟮jq⟯ := Polynomial.mapRingHom evalAtJGen with hθ
  have hθinj : Function.Injective θ := Polynomial.map_injective _ evalAtJGen_injective
  have haeval : Polynomial.aeval (jqN (ℓ * M)) (θ R) = 0 := by
    rw [hθ, Polynomial.coe_mapRingHom, Polynomial.aeval_def, Polynomial.eval₂_map,
      algebraMap_comp_evalAtJGen]
    exact hΞR
  have hmin : minpoly ℚ⟮jq⟯ (jqN (ℓ * M)) = θ dN.Φ := by
    rw [dN.minpoly_jqN_eq (phiIrreducible_all _ dN)]
    rfl
  have hdvd : θ dN.Φ ∣ θ R := by
    rw [← hmin]
    exact minpoly.dvd _ _ haeval

  rw [← Polynomial.modByMonic_eq_zero_iff_dvd dN.monic]
  apply hθinj
  rw [map_zero, hθ, Polynomial.coe_mapRingHom, Polynomial.map_modByMonic _ dN.monic,
    Polynomial.modByMonic_eq_zero_iff_dvd (dN.monic.map _)]
  exact hdvd

end S_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul (solution)
