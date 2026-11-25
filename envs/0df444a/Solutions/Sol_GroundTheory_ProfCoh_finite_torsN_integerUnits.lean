-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_torsN_integerUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:45.072742+00:00
-- url     : https://prove2.me/submissions/4ca76518-75a3-4673-a55a-5d2a55275542

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
omit [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
namespace GroundTheory.ProfCoh
theorem _root_.solution (l : ℕ) [NeZero l] : Finite (TorsN (Additive 𝒪[F]ˣ) l) := by
  classical
  have hl : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  have key : ∀ x : TorsN (Additive 𝒪[F]ˣ) l,
      (((x : Additive 𝒪[F]ˣ).toMul : 𝒪[F]ˣ) : 𝒪[F]) ∈ Polynomial.nthRootsFinset l (1 : 𝒪[F]) := by
    intro x
    rw [Polynomial.mem_nthRootsFinset hl, ← Units.val_pow_eq_pow_val, ← toMul_nsmul,
      (mem_ker_lsmul_iff l _).mp x.2]
    rfl
  refine Finite.of_injective
    (fun x : TorsN (Additive 𝒪[F]ˣ) l ↦
      (⟨_, key x⟩ : (Polynomial.nthRootsFinset l (1 : 𝒪[F]) : Set 𝒪[F]))) ?_
  intro x y h
  exact Subtype.ext (Additive.toMul.injective (Units.ext (congrArg Subtype.val h)))
end GroundTheory.ProfCoh
