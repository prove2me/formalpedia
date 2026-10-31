-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:23:00.920911+00:00
-- url     : https://prove2.me/submissions/9d2fba2f-51e8-4e6b-81fd-0c46597f3f1f

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_residual_good

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

theorem eWord {n : ℕ} {m : Mat3} (h : GoodWord n m) :
    ∃ w : List E, w.prod = eInterpret m ∧ w.length ≤ n ∧ ∀ s ∈ w, s ∈ eGenSet := by
  obtain ⟨hd,w,hw,hlen,hmem⟩ := h
  let f (s : {s // s ∈ w}) : E := ⟨s.1, Subgroup.subset_closure (hmem _ s.2)⟩
  refine ⟨w.attach.map f, ?_, by simpa using hlen, ?_⟩
  · apply Subtype.ext
    change elementary.subtype ((w.attach.map f).prod) = (eInterpret m : SL)
    rw [map_list_prod, List.map_map]
    simp only [Function.comp_def]
    have he : w.attach.map (fun s => elementary.subtype (f s)) = w := by
      simpa only [f, Subgroup.coe_subtype, List.map_id_fun, id_eq] using
        (List.attach_map_val (l := w) (f := id))
    rw [he, hw, eInterpret_coe ⟨hd,w,hw,hlen,hmem⟩]
  · intro s hs
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hs
    exact mem_eGenSet.mpr (hmem _ t.2)

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem residualInE_support_oai : ∀ p ∈ residualInE, ∃ w : List E,
    w.prod = p.1 ∧ w.length ≤ 4 ∧ ∀ s ∈ w, s ∈ eGenSet := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact eWord (residual_good hq)

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_support_oai := @OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_support_oai
