-- Prove2me | solution 1 for John.isCompact_contact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:07:38.531197+00:00
-- url     : https://prove2.me/submissions/4bbd4bd9-0394-4acf-ba9b-0fb7af504400

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
namespace John
theorem _root_.solution (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    IsCompact (Contact q) := by
  have hsub : Contact q ⊆ Metric.sphere 0 1 := fun u hu => by
    simpa using hu.1
  have hcl : IsClosed (Contact q) := by
    have heq : Contact q =
        {u : EuclideanSpace 𝕜 (Fin k) | ‖u‖ = 1} ∩ ⋂ x, {u | re ⟪x, u⟫_𝕜 ≤ q x} := by
      ext u
      simp only [Contact, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [heq]
    refine (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_iInter fun x => isClosed_le ?_ continuous_const)
    exact RCLike.continuous_re.comp (continuous_const.inner continuous_id)
  exact (isCompact_sphere 0 1).of_isClosed_subset hcl hsub
end John
