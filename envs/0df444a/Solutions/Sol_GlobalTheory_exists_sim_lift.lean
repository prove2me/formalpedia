-- Prove2me | solution 1 for GlobalTheory.exists_sim_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:44.28869+00:00
-- url     : https://prove2.me/submissions/73bf9f7c-c3d3-4b16-9479-7b79b0bb9c7f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Theorems.Thm_GlobalTheory_SimLift_modN_of_dvd_modulus
import Theorems.Thm_GlobalTheory_SimLift_modN_trans
import Theorems.Thm_GlobalTheory_SimLift_IsSimMod_of_dvd
import Theorems.Thm_GlobalTheory_SimLift_step
import Theorems.Thm_GlobalTheory_SimLift_exists_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
open SimLift
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (N : ℕ)
    (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
    (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
    ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν := by
  intro E _ _ _ H D N f ν hN hc hf
  let T : ℕ → Type := fun k =>
    {x : (D.La →ₗ[𝓞 E] D.La) × ℤ // IsSimMod D (N * k.factorial) x.1 x.2}
  have hstep : ∀ k (x : T k), ∃ y : T (k + 1),
      (∀ a, D.ModN (N * k.factorial) (y.1.1 a - x.1.1 a)) ∧ ((N * k.factorial : ℕ) : ℤ) ∣ y.1.2 - x.1.2 := by
    intro k x
    obtain ⟨f', ν', h1, h2⟩ := step D (k + 1) k.succ_pos _ (Nat.mul_pos hN k.factorial_pos) _ _ x.2
    refine ⟨⟨(f', ν'), ?_⟩, h2⟩
    rwa [Nat.factorial_succ, Nat.mul_comm (k + 1), ← Nat.mul_assoc]
  choose nx hnx using hstep
  let s : ∀ k, T k := fun k => Nat.rec (⟨(f, ν), by
    rw [Nat.factorial_zero, Nat.mul_one]; exact ⟨hc, hf⟩⟩ : T 0) nx k
  have hs : ∀ k j, k ≤ j → (∀ a, D.ModN (N * k.factorial) ((s j).1.1 a - (s k).1.1 a)) ∧
      ((N * k.factorial : ℕ) : ℤ) ∣ (s j).1.2 - (s k).1.2 := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact ⟨fun a => ⟨0, by simp⟩, by simp⟩
    | succ j hkj ih =>
      have hd : N * k.factorial ∣ N * j.factorial :=
        Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial hkj)
      obtain ⟨h1, h2⟩ := hnx j (s j)
      refine ⟨fun a => modN_trans D (modN_of_dvd_modulus D hd (h1 a)) (ih.1 a), ?_⟩
      have h3 := dvd_add ((Int.natCast_dvd_natCast.mpr hd).trans h2) ih.2
      rwa [sub_add_sub_cancel] at h3
  have hd : ∀ n, 0 < n → n ∣ N * n.factorial := fun n hn =>
    (Nat.dvd_factorial hn le_rfl).mul_left N
  refine ⟨⟨fun n => (s n).1.1, fun n => (s n).1.2, fun n m hn hm a => ?_, fun n hn => ?_,
    fun n hn => ?_⟩, fun a => ?_, ?_⟩
  · exact modN_of_dvd_modulus D (hd n hn) ((hs n _ (Nat.le_mul_of_pos_right n hm)).1 a)
  · exact exists_inv D hn ((s n).2.of_dvd D (hd n hn))
  · exact ((s n).2.of_dvd D (hd n hn)).2
  · exact modN_of_dvd_modulus D (dvd_mul_right N _) ((hs 0 N N.zero_le).1 a)
  · exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right N _)).trans (hs 0 N N.zero_le).2
end GlobalTheory
