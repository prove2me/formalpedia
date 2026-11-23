-- Prove2me | solution 1 for GlobalTheory.HeckeGal.isOpen_ker_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:21.1673+00:00
-- url     : https://prove2.me/submissions/d566a735-e4c7-432e-a770-db6143a9b59d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.HeckeGal
theorem _root_.solution {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [T1Space Kˣ]
    (φ : Γ →* Kˣ) (hφ : Continuous φ) {m : ℕ} (hm : 0 < m) (h : ∀ g, φ g ^ m = 1) : IsOpen (φ.ker : Set Γ) := by
  have : NeZero m := ⟨hm.ne'⟩
  have hfin : ((rootsOfUnity m K : Set Kˣ) \ {1}).Finite :=
    (Set.finite_coe_iff.mp (inferInstanceAs (Finite (rootsOfUnity m K)))).sdiff
  have e : (φ.ker : Set Γ) = (φ ⁻¹' ((rootsOfUnity m K : Set Kˣ) \ {1}))ᶜ := by
    ext g
    simp [MonoidHom.mem_ker, mem_rootsOfUnity, h g]
  rw [e]
  exact (hfin.isClosed.preimage hφ).isOpen_compl
end GlobalTheory.HeckeGal
