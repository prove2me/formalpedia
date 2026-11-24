-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.mem_of_genU_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:28.948721+00:00
-- url     : https://prove2.me/submissions/514f0f99-f662-4d43-8e35-5521ca70f486

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_FrameMatrixChartRatios

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
variable {Ω : Type} [Field Ω] {S : Type} {r : S → ℕ}
variable {E : Type} [AddCommGroup E] [Module Ω E] {n : S → ℕ}
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
theorem _root_.solution (L : Subfield (GenField Ω r)) (hbase : ∀ b : Ω, algebraMap Ω (GenField Ω r) b ∈ L)
    (hentry : ∀ (s : S) (k l : Fin (r s)), k ≤ l → genU Ω r s l k ∈ L) (a : GenField Ω r) : a ∈ L := by
  have hpoly : ∀ p : MvPolynomial (GenIx r) Ω,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ L := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C b =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hbase b
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := i
      have := hentry s k l (le_of_lt h)
      rwa [genU, dif_pos h] at this
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (GenIx r) Ω) a
  exact div_mem (hpoly p) (hpoly q)
end GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen
