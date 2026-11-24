-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.finite_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:22:57.967433+00:00
-- url     : https://prove2.me/submissions/60fbe0ee-718a-4b5d-8015-9b3795126ae1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear
import Theorems.Thm_GlobalTheory_AdLat_RootNear_unit_of_integral
import Theorems.Thm_GlobalTheory_AdLat_RootNear_exists_idem
import Theorems.Thm_GlobalTheory_AdLat_RootNear_inclHat_integral
import Theorems.Thm_GlobalTheory_AdLat_RootNear_half_root
import Theorems.Thm_GlobalTheory_T_exists_integral_unit_root_norm_one_adele


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) (n : ℕ)
    (u z : RA F E) (hz : z ∈ intHat F E) (huz : u - 1 = (2 * n) • z)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) :
    ∃ x y : RA F E, x * y = 1 ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x ∧
      (∃ p ∈ intHat F E, x = 1 + n • p) ∧ ∃ p ∈ intHat F E, y = 1 + n • p := by
  have hu1 : u = 1 + 2 * n * z := by
    rw [nsmul_eq_mul] at huz
    push_cast at huz
    linear_combination huz
  have huO : u ∈ intHat F E := by
    rw [hu1]
    exact add_mem (one_mem _) (mul_mem (mul_mem (ofNat_mem _ 2) (natCast_mem _ n)) hz)
  obtain ⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩ := GlobalTheory.T.exists_integral_unit_root_norm_one_adele F E c h2 hc hP u huO hu
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n
  obtain ⟨y₀, hy₀⟩ := (unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun ⟨z, hz⟩).exists_right_inv
  have hr₀ : (1 + n * z) = u * sg (FiniteAdeleRing (𝓞 F) F) c (1 + n * z) :=
    half_root F E c u _ hu (by rw [hu1]; ring)
  have hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E) := by
    change sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)
    simp [sg]
  have hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e := by
    rw [← Subring.coe_mul, ← map_mul, hee]
  have hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hef
    simpa using this
  have hy₀' : (1 + (inclHat F E e : RA F E) * n * z) * y₀ = 1 := by
    have := congrArg (fun t : intHat F E => (t : RA F E)) hy₀
    simpa using this
  have heO := (inclHat F E e).2
  have hfO := (inclHat F E f).2
  have hy₀O := y₀.2
  generalize (inclHat F E e : RA F E) = e' at *
  generalize (inclHat F E f : RA F E) = f' at *
  generalize (y₀ : RA F E) = y' at *
  have hx₁' : x₁ ∈ intHat F E := hx₁
  have hy₁' : y₁ ∈ intHat F E := hy₁
  have hxy : (e' * (1 + n * z) + (1 - e') * x₁) * (e' * y' + (1 - e') * y₁) = 1 := by
    linear_combination e' * hy₀' + (1 - e') * hxy₁ +
      (y' - (1 + n * z) * y₁ - x₁ * y' + x₁ * y₁) * hee'
  have hp : e' * z + f' * (x₁ - 1) ∈ intHat F E :=
    add_mem (mul_mem heO hz) (mul_mem hfO (sub_mem hx₁' (one_mem _)))
  have hx : e' * (1 + n * z) + (1 - e') * x₁ = 1 + n * (e' * z + f' * (x₁ - 1)) := by
    linear_combination (x₁ - 1) * hef'
  refine ⟨_, _, hxy, ?_, ⟨_, hp, by rw [nsmul_eq_mul]; exact hx⟩,
    -((e' * y' + (1 - e') * y₁) * (e' * z + f' * (x₁ - 1))), ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, map_sub, map_one, hse]
    linear_combination e' * hr₀ + (1 - e') * hr₁
  · exact neg_mem (mul_mem (add_mem (mul_mem heO hy₀O) (mul_mem (sub_mem (one_mem _) heO) hy₁')) hp)
  · rw [nsmul_eq_mul]
    rw [hx] at hxy
    linear_combination hxy
end GlobalTheory.AdLat.RootNear
