-- Prove2me | solution 1 for ModularCurve.finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/81c2e911-42dc-5be5-b976-7f0610ceaf2b

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
open ModularCurve IntermediateField Polynomial
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N)) :
    FiniteDimensional
      (IntermediateField.adjoin K
        ({(⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N)} : Set (modularFunctionFieldC K N)))
      (modularFunctionFieldC K N) ∧
    Algebra.IsSeparable
      (IntermediateField.adjoin K
        ({(⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N)} : Set (modularFunctionFieldC K N)))
      (modularFunctionFieldC K N) := by
  set F := modularFunctionFieldC K N with hF
  let jF : F := ⟨jqModC K, jqModC_mem K N⟩
  let jNF : F := ⟨jqNModC K N, jqNModC_mem K N⟩
  have htr : Transcendental K jF := by
    intro halg
    exact (transcendental_jqModC K) (halg.algHom (IsScalarTower.toAlgHom K F (LaurentSeries K)))
  let L := LaurentSeries K
  let φ : F →ₐ[K] L := IsScalarTower.toAlgHom K F L
  have hφ : Function.Injective φ := Subtype.val_injective

  have hsepF : IsSeparable (K⟮jF⟯ : IntermediateField K F) jNF := by
    have hmap : (K⟮jF⟯ : IntermediateField K F).toSubalgebra.map φ
        = (K⟮jqModC K⟯ : IntermediateField K L).toSubalgebra := by
      rw [← IntermediateField.toSubalgebra_map, IntermediateField.adjoin_map,
        Set.image_singleton]
      rfl
    let eMI := (K⟮jF⟯ : IntermediateField K F).toSubalgebra.equivMapOfInjective φ hφ
    let eOE := Subalgebra.equivOfEq _ _ hmap
    let e : (K⟮jqModC K⟯ : IntermediateField K L) ≃ₐ[K] (K⟮jF⟯ : IntermediateField K F) :=
      (eMI.trans eOE).symm
    have hcompat : ∀ a, φ ↑(e a) = (a : L) := fun a => by
      have step : eMI (e a) = eOE.symm a := eMI.apply_symm_apply (eOE.symm a)
      calc φ ↑(e a)
          = ↑(eMI (e a)) := (Subalgebra.coe_equivMapOfInjective_apply _ _ hφ _).symm
        _ = ↑(eOE.symm a) := by rw [step]
        _ = (a : L) := rfl
    refine (Polynomial.Separable.map hsep (f := e.toRingEquiv.toRingHom)).of_dvd (minpoly.dvd _ jNF ?_)
    have key : (φ : ↥F →+* L)
        (Polynomial.aeval jNF
          ((minpoly ↥K⟮jqModC K⟯ (jqNModC K N)).map
            e.toRingEquiv.toRingHom)) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
      have hrh : ((φ : ↥F →+* L).comp ((algebraMap ↥K⟮jF⟯ ↥F).comp
            e.toRingEquiv.toRingHom))
          = algebraMap ↥K⟮jqModC K⟯ L :=
        RingHom.ext fun a => hcompat a
      rw [hrh]; exact minpoly.aeval _ _
    exact hφ (by rw [map_zero]; exact key)

  have hgen : (K⟮jF⟯ : IntermediateField K F)⟮jNF⟯
      = (⊤ : IntermediateField (K⟮jF⟯ : IntermediateField K F) F) := by
    have hadj2 : IntermediateField.adjoin K ({jF, jNF} : Set F) = ⊤ := by
      have hmap2 : (IntermediateField.adjoin K ({jF, jNF} : Set F)).map φ = F := by
        rw [IntermediateField.adjoin_map, Set.image_insert_eq, Set.image_singleton]
        rfl
      rw [eq_top_iff]; intro y _
      have hy : (y : L) ∈ (IntermediateField.adjoin K ({jF, jNF} : Set F)).map φ := by
        rw [hmap2]; exact y.2
      obtain ⟨w, hw, hφw⟩ := (IntermediateField.mem_map _).mp hy
      exact (hφ (show φ w = φ y from hφw) : w = y) ▸ hw
    have hset : ({jF, jNF} : Set F) = {jF} ∪ {jNF} := Set.insert_eq _ _
    rw [hset, ← IntermediateField.adjoin_adjoin_left] at hadj2
    haveI : IsScalarTower K (K⟮jF⟯ : IntermediateField K F) F := by infer_instance
    exact IntermediateField.restrictScalars_injective K
      (hadj2.trans (IntermediateField.restrictScalars_top (K := K)).symm)
  have hfd : FiniteDimensional (K⟮jF⟯ : IntermediateField K F) F := by
    haveI : FiniteDimensional (K⟮jF⟯ : IntermediateField K F)
        ((K⟮jF⟯ : IntermediateField K F)⟮jNF⟯) :=
      IntermediateField.adjoin.finiteDimensional hsepF.isIntegral
    haveI : FiniteDimensional (K⟮jF⟯ : IntermediateField K F)
        (⊤ : IntermediateField (K⟮jF⟯ : IntermediateField K F) F) := hgen ▸ this
    exact (IntermediateField.topEquiv (F := (K⟮jF⟯ : IntermediateField K F)) (E := F))
      |>.toLinearEquiv.finiteDimensional
  haveI hadj : Algebra.IsSeparable (K⟮jF⟯ : IntermediateField K F)
      ((K⟮jF⟯ : IntermediateField K F)⟮jNF⟯) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hsepF
  haveI htop : Algebra.IsSeparable (K⟮jF⟯ : IntermediateField K F)
      (⊤ : IntermediateField (K⟮jF⟯ : IntermediateField K F) F) := hgen ▸ hadj
  have hsepAlg : Algebra.IsSeparable (K⟮jF⟯ : IntermediateField K F) F :=
    AlgEquiv.Algebra.isSeparable
      (IntermediateField.topEquiv (F := (K⟮jF⟯ : IntermediateField K F)) (E := F))
  exact ⟨hfd, hsepAlg⟩

end
end S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
end P2MW
export P2MW.S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC (solution)
