-- Prove2me | solution 1 for OAI.Laughlin.Fock.truncatedScalingInv_coordinate_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:34:09.80527+00:00
-- url     : https://prove2.me/submissions/be9e881e-7c3b-4267-956e-a74dfca1bafb

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_ScalingWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem orbitalScaling_mode (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    orbitalScaling Q d (mode i) = d i • mode i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [orbitalScaling,mode]
  · simp [orbitalScaling,mode,h]

theorem exteriorScaling_wedge (Q n : ℕ) (d : Fin (Q+1) → ℂ) (w : Fin n → Fin (Q+1)) :
    exteriorScaling Q d (ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a))) =
      (∏ a, d (w a)) • ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a)) := by
  unfold exteriorScaling
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ n (fun a => orbitalScaling Q d (mode (w a))) = _
  simp_rw [orbitalScaling_mode]
  exact (ExteriorAlgebra.ιMulti ℂ n).map_smul_univ (fun a => d (w a)) (fun a => mode (w a))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_OccupationDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_product (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    (∏ a : Fin n, d (Set.powersetCard.ofFinEmbEquiv.symm A a)) = ∏ i ∈ A.val, d i := by
  apply Finset.prod_bij (fun a _ => Set.powersetCard.ofFinEmbEquiv.symm A a)
  · intro a ha
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A _).mp ⟨a,rfl⟩
  · intro a ha b hb hab
    exact (Set.powersetCard.ofFinEmbEquiv.symm A).injective hab
  · intro b hb
    obtain ⟨a,ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A b).mpr hb
    exact ⟨a, Finset.mem_univ a, ha⟩
  · intro a ha
    rfl

theorem exteriorScaling_occupation_sector (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    exteriorScaling Q d (occupationBasis Q A.val) =
      (∏ i ∈ A.val, d i) • occupationBasis Q A.val := by
  have h := exteriorScaling_wedge Q n d (Set.powersetCard.ofFinEmbEquiv.symm A)
  rw [occupation_product Q n d A] at h
  simpa only [occupationBasis, ExteriorAlgebra.basis_apply_powersetCard,
    ExteriorAlgebra.ιMulti_family, Function.comp_def, Pi.basisFun_apply, mode] using h

theorem exteriorScaling_occupation (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Finset (Fin (Q+1))) :
    exteriorScaling Q d (occupationBasis Q A) = (∏ i ∈ A, d i) • occupationBasis Q A := by
  exact exteriorScaling_occupation_sector Q A.card d ⟨A,rfl⟩

theorem exteriorScaling_occupation_entry (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (A B : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (exteriorScaling Q d (occupationBasis Q A)) B =
      if A = B then ∏ i ∈ A, d i else 0 := by
  rw [exteriorScaling_occupation, map_smul]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

theorem exteriorScaling_coordinate (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (x : Space Q) (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (exteriorScaling Q d x) A =
      (∏ i ∈ A, d i)*(occupationBasis Q).repr x A := by
  have h : ((occupationBasis Q).coord A).comp (exteriorScaling Q d).toLinearMap =
      (∏ i ∈ A, d i) • (occupationBasis Q).coord A := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (exteriorScaling Q d (occupationBasis Q B)) A =
      (∏ i ∈ A, d i)*(occupationBasis Q).repr (occupationBasis Q B) A
    rw [exteriorScaling_occupation_entry]
    by_cases hBA : B = A
    · subst B
      simp
    · simp [Module.Basis.repr_self, hBA]
  exact LinearMap.congr_fun h x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_TruncatedScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem truncatedScalingInv_coordinate_s50_oai (L Q : ℕ) (x : Space Q) (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (truncatedScalingInv L Q x) A =
      ((truncatedDiagonals L Q A)⁻¹ : ℝ) * (occupationBasis Q).repr x A := by
  rw [truncatedScalingInv,exteriorScaling_coordinate]
  simp [truncatedDiagonals,Finset.prod_inv_distrib,Complex.ofReal_prod]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.truncatedScalingInv_coordinate_s50_oai := @OAI.Laughlin.Fock.truncatedScalingInv_coordinate_s50_oai
