-- Prove2me | solution 1 for OAI.NuclearUltrapower.Elementary.kazhdanSet_generates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:13:27.057792+00:00
-- url     : https://prove2.me/submissions/9cc4b830-c545-420d-be48-299ef74f3be9

import Mathlib
import Definitions.Def_OAIQ019N044

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
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.Elementary
open SOS

theorem translation_add (v w : IntegralVector3) :
    integralTranslation (v+w) = integralTranslation v * integralTranslation w := by
  exact map_mul SemidirectProduct.inl (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)

theorem translation_zsmul (v : IntegralVector3) (k : ℤ) :
    integralTranslation (k • v) = integralTranslation v ^ k := by
  exact map_zpow SemidirectProduct.inl (Multiplicative.ofAdd v) k

theorem translation_three (v : IntegralVector3) :
    integralTranslation v = integralTranslation (v 0 • basisVector 0) *
      integralTranslation (v 1 • basisVector 1) * integralTranslation (v 2 • basisVector 2) := by
  have hv : v = v 0 • basisVector 0 + v 1 • basisVector 1 + v 2 • basisVector 2 := by
    ext j
    fin_cases j <;> simp [basisVector]
  calc
    _ = integralTranslation (v 0 • basisVector 0 + v 1 • basisVector 1 + v 2 • basisVector 2) := congrArg _ hv
    _ = _ := by rw [translation_add, translation_add]

theorem normal_form (g : IntegralGroup) :
    g = integralTranslation g.left.toAdd * linearInclusion g.right := by
  exact (SemidirectProduct.inl_left_mul_inr_right g).symm

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary
open SOS SOSEnergy
open Displacement (dist)

theorem kazhdanSet_generates_oai : Subgroup.closure (kazhdanSet : Set IntegralGroup) = ⊤ := by
  classical
  let K := Subgroup.closure (kazhdanSet : Set IntegralGroup)
  have hlin : ∀ M : E, linearInclusion M ∈ K := by
    have he : (eGenSet : Set E) ⊆ K.comap linearInclusion := by
      intro M hM
      exact Subgroup.subset_closure (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨M,hM,rfl⟩))
    have hc := (Subgroup.closure_le (K.comap linearInclusion)).mpr he
    rw [eSet_generates] at hc
    exact fun M => hc (Subgroup.mem_top M)
  have hb (i : Fin 3) : integralTranslation (basisVector i) ∈ K :=
    Subgroup.subset_closure (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have ht : ∀ v, integralTranslation v ∈ K := by
    intro v
    rw [translation_three]
    exact K.mul_mem (K.mul_mem (by rw [translation_zsmul]; exact K.zpow_mem (hb 0) _)
      (by rw [translation_zsmul]; exact K.zpow_mem (hb 1) _))
      (by rw [translation_zsmul]; exact K.zpow_mem (hb 2) _)
  apply top_unique
  intro g _
  rw [normal_form g]
  exact K.mul_mem (ht _) (hlin _)

end NuclearUltrapower.Elementary
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.Elementary.kazhdanSet_generates_oai := @OAI.NuclearUltrapower.Elementary.kazhdanSet_generates_oai
