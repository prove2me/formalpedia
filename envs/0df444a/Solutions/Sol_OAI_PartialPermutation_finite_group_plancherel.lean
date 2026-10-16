-- Prove2me | solution 1 for OAI.PartialPermutation.finite_group_plancherel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:46:44.441811+00:00
-- url     : https://prove2.me/submissions/df70c18f-d4f7-4d92-b37b-ca33a5664e1b

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Plancherel.lean:L114-L148
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.finite_group_plancherel. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel

-- ---- from OAI.RepresentationTheory.PartialPermutation.Characters ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate

namespace PartialPermutation
open scoped BigOperators ComplexConjugate MonoidAlgebra

noncomputable section
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
include hρ

omit [Fintype G] in
lemma unitary_adjoint (g : G) : LinearMap.adjoint (ρ g) = ρ g⁻¹ := by
  ext v
  apply ext_inner_left ℂ
  intro u
  rw [LinearMap.adjoint_inner_right]
  have h := hρ g u (ρ g⁻¹ v)
  simpa using h

variable [Representation.IsIrreducible ρ]

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.RegularRepresentation ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
variable (G : Type*) [Group G] [Fintype G]

lemma regularRep_unitary (g : G) (f k : EuclideanSpace ℂ G) :
    inner ℂ (regularRep G g f) (regularRep G g k) = inner ℂ f k := by
  simp only [PiLp.inner_apply, regularRep_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun h => rfl)

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.Plancherel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
open scoped BigOperators MonoidAlgebra Classical

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
lemma componentRep_unitary {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (c : isotypicComponents ℂ[G] ρ.asModule) : IsUnitary (componentRep ρ c) := by
  intro g x y
  exact hρ g x.val y.val

lemma irreducibleRep_unitary (c : IrreducibleIndex G) :
    IsUnitary (G := G) (V := irreducibleSpace c) (irreducibleRep c) :=
  componentRep_unitary (regularRep G) (regularRep_unitary G) c

lemma regular_character_identity (g : G) :
    ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ) * (irreducibleRep c).character g =
      if g = 1 then (Fintype.card G : ℂ) else 0 := by
  have ht := congrArg (fun A : Module.End ℂ (EuclideanSpace ℂ G) => A (deltaOne G) g⁻¹)
    (sum_character_kernels_identity (regularRep G))
  rw [complexFourier_regular_delta] at ht
  change (∑ c : IrreducibleIndex G, centralCharacterKernel (irreducibleRep c) g⁻¹) =
    (deltaOne G) g⁻¹ at ht
  simp only [centralCharacterKernel, inv_inv] at ht
  have hN : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht' := congrArg (fun z : ℂ => (Fintype.card G : ℂ) * z) ht
  simp only [Finset.mul_sum] at ht'
  convert ht' using 1
  · apply Finset.sum_congr rfl
    intro c _
    change _ = (Fintype.card G : ℂ) *
      ((irreducibleDegree c : ℂ) / Fintype.card G * (irreducibleRep c).character g)
    field_simp
  · change (if g = 1 then (Fintype.card G : ℂ) else 0) =
      (Fintype.card G : ℂ) * (if g⁻¹ = 1 then 1 else 0)
    simp only [inv_eq_one]
    split_ifs <;> simp

lemma trace_fourier_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (a : G → ℂ) :
    LinearMap.trace ℂ V (LinearMap.adjoint (complexFourier ρ a) * complexFourier ρ a) =
      ∑ h, ∑ g, conj (a h) * a g * ρ.character (h⁻¹ * g) := by
  have hadj : LinearMap.adjoint (complexFourier ρ a) =
      ∑ h, conj (a h) • ρ h⁻¹ := by
    simp only [complexFourier, map_sum, map_smulₛₗ, unitary_adjoint ρ hρ]
  rw [hadj, complexFourier, Finset.sum_mul]
  simp only [map_sum, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_smul,
    smul_eq_mul, ← map_mul, Representation.character]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem finite_group_plancherel (a : G → ℂ) :
    (Fintype.card G : ℝ) * ∑ g, ‖a g‖^2 =
      ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℝ) *
        hsNormSq (V := irreducibleSpace c) (complexFourier (V := irreducibleSpace c) (irreducibleRep c) a) := by
  have he : ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ) *
      LinearMap.trace ℂ (irreducibleSpace c)
        (LinearMap.adjoint (𝕜 := ℂ) (E := irreducibleSpace c) (F := irreducibleSpace c) (complexFourier (V := irreducibleSpace c) (irreducibleRep c) a) *
          complexFourier (V := irreducibleSpace c) (irreducibleRep c) a) =
        (Fintype.card G : ℂ) * ∑ g, conj (a g) * a g := by
    have htrace (c : IrreducibleIndex G) := trace_fourier_energy
      (V := irreducibleSpace c) (irreducibleRep c) (irreducibleRep_unitary c) a
    simp only [htrace, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ h, ∑ g, conj (a h) * a g *
          (∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ) *
            (irreducibleRep c).character (h⁻¹ * g)) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := by
        simp only [regular_character_identity, inv_mul_eq_one]
        simp [mul_comm, mul_left_comm]
  have hre := congrArg Complex.re he
  have hnorm (g : G) : (conj (a g) * a g).re = ‖a g‖^2 := by
    rw [mul_comm, Complex.mul_conj]
    exact Complex.normSq_eq_norm_sq _
  simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, hnorm, hsNormSq] using hre.symm

end
end PartialPermutation
end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
open scoped BigOperators MonoidAlgebra Classical


theorem solution : type_of% @_root_.OAI.PartialPermutation.finite_group_plancherel := @_root_.OAI.PartialPermutation.finite_group_plancherel
