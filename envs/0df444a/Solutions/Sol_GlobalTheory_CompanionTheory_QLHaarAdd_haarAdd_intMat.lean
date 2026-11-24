-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLHaarAdd.haarAdd_intMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:52:02.425609+00:00
-- url     : https://prove2.me/submissions/1fb540e8-6c73-423b-81d2-f4c6b5613a6d

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalized
import Theorems.Thm_GlobalTheory_CompanionTheory_QLHaarAdd_eq_addHaar
import Theorems.Thm_GlobalTheory_T_localField_topology_norm_balls


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLHaarAdd
namespace GlobalTheory.CompanionTheory.QLHaarAdd
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, BorelSpace (Matrix (Fin n) (Fin m) F) ∧ IsOpen (intMat O n m) ∧ IsCompact (intMat O n m) ∧ (∃ dx : Measure (Matrix (Fin n) (Fin m) F), dx.IsAddLeftInvariant ∧ dx (intMat O n m) = 1) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx.IsAddHaarMeasure) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → ∀ (dy : Measure (Matrix (Fin n) (Fin m) F)), dy.IsAddLeftInvariant → dy (intMat O n m) = 1 → dx = dy) := by
  intro F _ _ _ _ _ _ O ϖ nrm q hLF n m
  obtain ⟨hOo, hOc, hsc, -, -, -⟩ := GlobalTheory.T.localField_topology_norm_balls hLF
  haveI : IsTopologicalRing F := inferInstance
  haveI : T2Space F := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have hset : intMat O n m = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin m => (O : Set F))) := by
    ext y; exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hopen : IsOpen (intMat O n m) := by
    rw [hset]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hOo
  have hcomp : IsCompact (intMat O n m) := by
    rw [hset]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc
  have h0 : (0 : Matrix (Fin n) (Fin m) F) ∈ intMat O n m := fun _ _ => O.zero_mem
  haveI hB : BorelSpace (Matrix (Fin n) (Fin m) F) :=
    inferInstanceAs (BorelSpace (Fin n → Fin m → F))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin m) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin m → F))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin m) F) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin m → F))
  let K₀ : TopologicalSpace.PositiveCompacts (Matrix (Fin n) (Fin m) F) :=
    ⟨⟨intMat O n m, hcomp⟩, ⟨0, mem_interior_iff_mem_nhds.2 (hopen.mem_nhds h0)⟩⟩
  have key : ∀ dx : Measure (Matrix (Fin n) (Fin m) F), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 →
      dx = Measure.addHaarMeasure K₀ := fun dx _ h => eq_addHaar K₀ hopen h0 dx h
  refine ⟨hB, hopen, hcomp, ⟨Measure.addHaarMeasure K₀, inferInstance, Measure.addHaarMeasure_self⟩, ?_, ?_⟩
  · intro dx hi h
    rw [key dx hi h]
    infer_instance
  · intro dx hi h dy hj h'
    rw [key dx hi h, key dy hj h']
end GlobalTheory.CompanionTheory.QLHaarAdd
