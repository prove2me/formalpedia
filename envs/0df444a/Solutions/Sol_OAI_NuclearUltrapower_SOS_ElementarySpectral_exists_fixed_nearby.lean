-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:20:26.505375+00:00
-- url     : https://prove2.me/submissions/ab445608-74af-488c-8136-ada228e04a7a

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_gap
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_delta_energy

section
-- module Solutions.OAIQ019_Nuc.Compat
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem generators_det : ∀ m ∈ generators, (toMatrix m).det = 1 := by
  decide +kernel

theorem goodWord_generator {m : Mat3} (hm : m ∈ generators) : GoodWord 1 m := by
  refine ⟨generators_det m hm, [interpret m], by simp, by simp, ?_⟩
  intro s hs
  have : s = interpret m := by simpa using hs
  subst s
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨m, hm, rfl⟩)

end NuclearUltrapower.SOS
end
end

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem goodWord_mem {n : ℕ} {m : Mat3} (h : GoodWord n m) : interpret m ∈ elementary := by
  obtain ⟨_, w, hw, _, hs⟩ := h
  rw [← hw]
  exact elementary.list_prod_mem (fun g hg => Subgroup.subset_closure (hs g hg))

theorem eInterpret_coe {n : ℕ} {m : Mat3} (h : GoodWord n m) :
    (eInterpret m : SL) = interpret m := by
  simp only [eInterpret, dite_eq_left (goodWord_mem h)]

theorem mem_eGenSet {g : E} : g ∈ eGenSet ↔ (g : SL) ∈ genSet := by
  constructor
  · intro h
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    rw [eInterpret_coe (goodWord_generator hm)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  · intro h
    obtain ⟨m, hm, he⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    apply List.mem_toFinset.mpr
    refine List.mem_map.mpr ⟨m,hm,?_⟩
    apply Subtype.ext
    exact (eInterpret_coe (goodWord_generator hm)).trans he

theorem eSet_generates : Subgroup.closure (eGenSet : Set E) = ⊤ := by
  apply top_unique
  intro g _
  let K := Subgroup.closure (eGenSet : Set E)
  have he : elementary ≤ K.map elementary.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro s hs
    have hs' : s ∈ elementary := Subgroup.subset_closure hs
    exact ⟨⟨s,hs'⟩, Subgroup.subset_closure (mem_eGenSet.mpr hs), rfl⟩
  obtain ⟨k,hk,hkg⟩ := he g.2
  have : k = g := Subtype.ext hkg
  exact this ▸ hk

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Kazhdan
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.supportComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem deltaOp_ker_fixed (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (deltaOp ρ).ker) :
    ∀ g : E, ρ g x = x := by
  have he := delta_energy ρ x
  change (inner ℂ x (deltaOp ρ x)).re = SOSEnergy.energy eGenSet ρ x / 2 at he
  have hx0 : deltaOp ρ x = 0 := hx
  rw [hx0, inner_zero_right, Complex.zero_re] at he
  have hs : SOSEnergy.energy eGenSet ρ x = 0 := by linarith
  have hf : (eGenSet : Set E) ⊆ vectorStabilizer ρ x := by
    intro g hg
    have hle : ‖ρ g x-x‖ ^ 2 ≤ SOSEnergy.energy eGenSet ρ x :=
      Finset.single_le_sum (fun s _ => sq_nonneg ‖ρ s x-x‖) hg
    rw [hs] at hle
    have hz : ‖ρ g x-x‖ = 0 := by nlinarith [norm_nonneg (ρ g x-x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hfull := (Subgroup.closure_le (vectorStabilizer ρ x)).mpr hf
  rw [eSet_generates] at hfull
  exact fun g => hfull (Subgroup.mem_top g)

/-- The constructive quantitative projection consequence actually used in the
semidirect-product proof. It does not assume a Kazhdan pair. -/
theorem exists_fixed_nearby_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    ∃ y : H, (∀ g : E, ρ g y = y) ∧
      (1/10 : ℝ) * ‖x-y‖ ^ 2 ≤ SOSEnergy.energy eGenSet ρ x := by
  let K := (deltaOp ρ).ker
  let y := K.starProjection x
  have hy : y ∈ K := K.starProjection_apply_mem x
  have hfix := deltaOp_ker_fixed ρ y hy
  refine ⟨y,hfix,?_⟩
  have hp := deltaOp_gap ρ (x-y) (K.sub_starProjection_mem_orthogonal x)
  have he : SOSEnergy.energy eGenSet ρ (x-y) = SOSEnergy.energy eGenSet ρ x := by
    unfold SOSEnergy.energy
    apply Finset.sum_congr rfl
    intro s _
    rw [map_sub, hfix s]
    congr 2
    abel
  exact he ▸ hp

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.exists_fixed_nearby_oai.{u_1}
