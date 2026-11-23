-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.exists_fromSpec_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:44.690592+00:00
-- url     : https://prove2.me/submissions/ea9d31da-7cab-4fd1-a8df-76b819657f1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency false
omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
namespace GlobalTheory.AffineQuotient
theorem _root_.solution [IsAffineHom f] (x : X) :
    ∃ (U : Y.affineOpens) (z : Spec Γ(X, f ⁻¹ᵁ U.1)), (U.2.preimage f).fromSpec z = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  refine ⟨⟨U, hU⟩, ?_⟩
  change x ∈ Set.range _
  rw [IsAffineOpen.range_fromSpec]
  exact hx
end GlobalTheory.AffineQuotient
