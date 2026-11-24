-- Prove2me | solution 1 for GlobalTheory.FunObj.DiagLattice.exists_KO_of_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:47:10.249697+00:00
-- url     : https://prove2.me/submissions/49b34d51-21ba-4e50-8aa9-dcb09f94ef63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.DiagLattice
namespace GlobalTheory.FunObj.DiagLattice
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k)
    (h1 : ∀ i j, M i j ∈ 𝒪[k]) (h2 : valuation k M.det = 1) : ∃ g ∈ KO k ι, g.val = M := by
  let A : Matrix ι ι 𝒪[k] := fun i j => ⟨M i j, h1 i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = M := rfl
  have hd : algebraMap 𝒪[k] k A.det = M.det := by rw [RingHom.map_det, hA]
  have hu : IsUnit A.det :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation k))).2 (by rw [hd, h2])
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨Matrix.GeneralLinearGroup.map (n := ι) (algebraMap 𝒪[k] k) u, ⟨u, rfl⟩, ?_⟩
  change u.val.map (algebraMap 𝒪[k] k) = _
  rw [hu]; rfl
end GlobalTheory.FunObj.DiagLattice
