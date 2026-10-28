-- Prove2me | solution 1 for OAI.Kadison.NormalGNS.matrix_stages_gns
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:40:59.448556+00:00
-- url     : https://prove2.me/submissions/b68ec22d-b9dc-4f22-82d2-adf853346250

import Mathlib
import Definitions.Def_OAIQ039C061
import Theorems.Thm_OAI_Kadison_NormalGNS_image_bicommutant

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNSClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
  (hSM : S≤M.toStarSubalgebra)
  (N : VonNeumannAlgebra τ.GNS)
  (hSN : ∀ a : M,(a:H →L[ℂ] H)∈S → τ.gnsStarAlgHom a∈N)

include hnormal hSM hSN in
lemma image_bicommutant_general (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈N := by
  let C : Set M := {a | τ.gnsStarAlgHom a∈N}
  have hC : IsClosed C := (VonNeumannCStar.isClosed N).preimage (map_continuous τ.gnsStarAlgHom)
  have hvalC : IsClosed ((Subtype.val : M → (H →L[ℂ] H)) '' C) :=
    (VonNeumannCStar.isClosed M).isClosedMap_subtype_val C hC
  have hSC : (S : Set (H →L[ℂ] H)) ⊆ (Subtype.val : M → (H →L[ℂ] H)) '' C := by
    intro a ha
    exact ⟨⟨a,hSM ha⟩,hSN ⟨a,hSM ha⟩ ha,rfl⟩
  have hcl := closure_minimal hSC hvalC
  have hSM' : S.topologicalClosure≤M.toStarSubalgebra :=
    S.topologicalClosure_minimal hSM (VonNeumannCStar.isClosed M)
  have hSN' (b : M) (hb : (b:H →L[ℂ] H)∈S.topologicalClosure) : τ.gnsStarAlgHom b∈N := by
    have hbcl : (b:H →L[ℂ] H)∈closure (S : Set (H →L[ℂ] H)) := hb
    obtain ⟨c,hc,hcb⟩ := hcl hbcl
    have he : c=b := Subtype.ext hcb
    change τ.gnsStarAlgHom c∈N at hc
    simpa only [he] using hc
  apply image_bicommutant M τ hnormal S.topologicalClosure S.isClosed_topologicalClosure hSM' N hSN' a
  intro T hT
  apply ha T
  intro b hb
  exact hT b (S.le_topologicalClosure hb)

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixStageGNSGeneration
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] M)

lemma representedStages_le : representedStages M I φ≤M.toStarSubalgebra := by
  apply iSup_le
  intro n
  rintro a ⟨b,rfl⟩
  exact (φ n b).property

include hnormal in
theorem matrix_stages_gns_oai (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (representedStages M I φ : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈Set.centralizer (Set.centralizer
      (TracialGNS.stageAlgebra τ I φ : Set _)) := by
  let S := TracialGNS.stageAlgebra τ I φ
  let N := bicommutant S
  let T := (N.toStarSubalgebra.comap τ.gnsStarAlgHom).map M.toStarSubalgebra.subtype
  have hST : representedStages M I φ≤T := by
    apply iSup_le
    intro n
    rintro x ⟨b,rfl⟩
    refine ⟨φ n b,?_,rfl⟩
    exact subset_bicommutant S
      ((le_iSup (TracialGNS.operatorStage τ I φ) n) ⟨b,rfl⟩)
  have hSN (b : M) (hb : (b:H →L[ℂ] H)∈representedStages M I φ) :
      τ.gnsStarAlgHom b∈N := by
    obtain ⟨c,hc,hcb⟩ := hST hb
    have he : c=b := Subtype.ext hcb
    change τ.gnsStarAlgHom c∈N at hc
    simpa only [he] using hc
  exact (mem_bicommutant S _).mp
    (image_bicommutant_general M τ hnormal (representedStages M I φ)
      (representedStages_le M I φ) N hSN a ha)

end Kadison.NormalGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.NormalGNS.matrix_stages_gns_oai.{u_1, u_2} := @OAI.Kadison.NormalGNS.matrix_stages_gns_oai.{u_1, u_2}
