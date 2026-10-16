-- Prove2me | solution 1 for OAI.TreeEdit.TorusFourier.displacement_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:10:40.678465+00:00
-- url     : https://prove2.me/submissions/30f172a9-4505-4c60-b4ee-a52421fa3a37

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/SampledSpectrum.lean:L278-L299
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusFourier.displacement_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Theorems.Thm_OAI_TreeEdit_FiniteFourier_l1_displacement_spectrum
import Theorems.Thm_OAI_TreeEdit_TorusFourier_mass_bound

-- ---- from OAI.Combinatorics.TreeEdit.FiniteFourier ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteFourier

open scoped ComplexConjugate
open RCLike

variable {A : Type*} [Fintype A] [AddCommGroup A]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

lemma multiplier_le_four (χ : AddChar A ℂ) (z : A) : multiplier χ z ≤ 4 := by
  have hn : ‖1 - χ z‖ ≤ 2 := by
    have hh := norm_sub_le (1 : ℂ) (χ z)
    rw [norm_one, χ.norm_apply] at hh
    norm_num at hh
    exact hh
  dsimp [multiplier]
  nlinarith [norm_nonneg (1 - χ z)]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

end FiniteFourier

namespace FiniteFourier

variable {A : Type*} [Fintype A] [AddCommGroup A]

lemma average_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

end FiniteFourier

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleFourier ----
namespace OAI

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical
open TorusTree

lemma character_one {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) : χ 1 = 1 ↔ χ = 0 := by
  constructor
  · intro h
    ext x
    rw [← ZMod.natCast_zmod_val x,
      show (x.val : ZMod M) = x.val • (1 : ZMod M) by simp [nsmul_eq_mul],
      AddChar.map_nsmul_eq_pow, h, one_pow]
    rfl
  · rintro rfl
    rfl

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree

end TreeEdit.TorusFourier

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.SampledSpectrum ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

lemma active_summary {M m : ℕ} [NeZero M] (h : ℕ) (χ : AddChar (State (ZMod M) m h) ℂ) :
    active χ (diagonal (A := ZMod M) (m := m) h 1) = if summary h χ = 0 then 0 else 1 := by
  have he : χ (diagonal (A := ZMod M) (m := m) h 1) = 1 ↔ summary h χ = 0 := character_one (summary h χ)
  unfold active
  simp only [he]

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

lemma energy_diagonal_le_mass {M m h : ℕ} [NeZero M]
    (H : AddChar (State (ZMod M) m h) ℂ → ℝ) (hH : ∀ χ, 0 ≤ H χ) (a : ZMod M) :
    energy H (diagonal (A := ZMod M) (m := m) h a) ≤ 4 * activeMass H (diagonal (A := ZMod M) (m := m) h 1) := by
  rw [energy, activeMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro χ _
  rw [active_summary]
  split_ifs with hc
  · have he : χ (diagonal (A := ZMod M) (m := m) h a) = 1 := congrArg (fun η : AddChar (ZMod M) ℂ => η a) hc
    simp only [multiplier, he, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero, le_refl]
  · simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right (multiplier_le_four χ _) (hH χ)

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

theorem displacement_bound {I : Type} {g s L M T R D Q J V b e K h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g ↪ I) (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M) (hPV : ∀ σ : Equiv.Perm I, period r j σ ≤ V) (hVT : V ≤ T)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R*D) (hMQ : M = J*Q)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQpow : Q ≤ b^e) (hg : e+K ≤ g) (hK : 1 ≤ K)
    (hM : (g*s+1)*Q < M) (C : Config I L (g*s) h) (t : ZMod M)
    (F : State (ZMod M) (g*s) h → RealL1) (a : ℝ) (ha : 0 ≤ a)
    (hlip : ∀ x y, dist (F x) (F y) ≤ a * ed (sampledWord r j T R h C x).val (sampledWord r j T R h C y).val) :
    average (fun x => dist (F x) (F (x + diagonal (A := ZMod M) (m := g*s) h t))) ≤
      a * FiniteTree.length (g*s) T h * (4*((K : ℝ)⁻¹^h + h*(2*(R : ℝ)/Q + 2*(V : ℝ)/T))) := by
  obtain ⟨H, hH, _, he⟩ := l1_displacement_spectrum F
  have hbound : SpectralBound (R := R) r j T h C H a := by
    intro z
    rw [energy, ← he]
    have hh := average_mono (fun x => hlip x (x+z))
    simpa only [dist_comm, average, mean, ← Finset.mul_sum, mul_assoc, mul_left_comm] using hh
  have hh := mass_bound r j hr hinj hPM hPV hVT hD hQ hMR hMQ hb hlower hQpow hg hK hM C H a hH ha hbound
  calc
    _ = energy H (diagonal (A := ZMod M) (m := g*s) h t) := by simpa only [dist_comm, energy] using he (diagonal (A := ZMod M) (m := g*s) h t)
    _ ≤ 4*activeMass H (diagonal (A := ZMod M) (m := g*s) h 1) := energy_diagonal_le_mass H hH t
    _ ≤ 4*(a * FiniteTree.length (g*s) T h * ((K : ℝ)⁻¹^h + h*(2*(R : ℝ)/Q + 2*(V : ℝ)/T))) := by gcongr
    _ = _ := by ring

end TreeEdit.TorusFourier

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusFourier.displacement_bound := @_root_.OAI.TreeEdit.TorusFourier.displacement_bound
