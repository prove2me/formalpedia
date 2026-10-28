-- Prove2me | solution 1 for OAI.Kadison.exists_separable_cstar_bicommutant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:54:27.777628+00:00
-- url     : https://prove2.me/submissions/f3b1a377-2b37-4c4e-8a43-8beb3a53211c

import Mathlib
import Definitions.Def_OAIQ039C026
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_exists_countable_strong_contraction_tests

section
-- module Solutions.OAIQ039_CM.Commutator_DenseCommutes
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutes_of_dense_contraction_tests (P : VonNeumannAlgebra H)
    (test : ℕ → H →L[ℂ] H)
    (hdense : ∀ A : H →L[ℂ] H,A∈P → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) ξ) atTop (𝓝 (A ξ)))
    (B : H →L[ℂ] H) (htest : ∀ n,Commute (test n) B)
    (A : H →L[ℂ] H) (hA : A∈P) : Commute A B := by
  let d : ℂ := ((‖A‖+1:ℝ):ℂ)
  have hdR : 0<‖A‖+1 := by positivity
  have hd : d≠0 := by
    dsimp only [d]
    exact_mod_cast (ne_of_gt hdR)
  have hdn : ‖d⁻¹ • A‖≤1 := by
    rw [norm_smul,norm_inv]
    have hnd : ‖d‖=‖A‖+1 := by
      dsimp only [d]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hdR]
    rw [hnd]
    have hi : (‖A‖+1)⁻¹*‖A‖=‖A‖/(‖A‖+1) := by ring
    rw [hi]
    exact (div_le_one hdR).mpr (by linarith)
  obtain ⟨k,hk⟩ := hdense (d⁻¹ • A) (P.smul_mem hA d⁻¹) hdn
  have hlim (x y : H) : Tendsto (fun n => inner ℂ (test (k n) x) y) atTop
      (𝓝 (inner ℂ ((d⁻¹ • A) x) y)) := (hk x).inner tendsto_const_nhds
  have hc := WeakOperatorLimit.intertwine hlim B B
    (Eventually.of_forall (fun n => (htest (k n)).eq))
  have h := congrArg (fun C : H →L[ℂ] H => d • C) hc
  change A*B=B*A
  simpa only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_inv_cancel₀ hd,one_smul] using h

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountablyGeneratedCStar
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison

lemma countable_submonoidClosure {A : Type*} [Monoid A] {s : Set A} (hs : s.Countable) :
    (Submonoid.closure s : Set A).Countable := by
  let := hs.to_subtype
  rw [Submonoid.closure_eq_mrange,MonoidHom.coe_mrange]
  exact Set.countable_range _

lemma separable_starAdjoin {A : Type*} [CStarAlgebra A] {s : Set A} (hs : s.Countable) :
    TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have hss : (s ∪ star s).Countable := hs.union (by simpa only [Set.image_star] using hs.image star)
  have hh := ((countable_submonoidClosure hss).isSeparable.span (R:=ℂ))
  have he : (StarAlgebra.adjoin ℂ s : Set A)=
      (Submodule.span ℂ (Submonoid.closure (s∪star s) : Set A) : Set A) :=
    congrArg (fun M : Submodule ℂ A => (M:Set A)) (StarAlgebra.adjoin_eq_span (R:=ℂ) s)
  rwa [he]

theorem exists_separable_cstar_bicommutant_oai
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (P : VonNeumannAlgebra H) :
    ∃ S : StarSubalgebra ℂ (H →L[ℂ] H),IsClosed (S:Set (H →L[ℂ] H)) ∧
      TopologicalSpace.SeparableSpace S ∧ S≤P.toStarSubalgebra ∧ NormalGNS.bicommutant S=P := by
  obtain ⟨test,ht,hd⟩ := exists_countable_strong_contraction_tests P
  let S := (StarAlgebra.adjoin ℂ (Set.range test)).topologicalClosure
  have hclosed : IsClosed (S:Set (H →L[ℂ] H)) := StarSubalgebra.isClosed_topologicalClosure _
  have hsep : TopologicalSpace.SeparableSpace S := by
    apply TopologicalSpace.IsSeparable.separableSpace
    exact (separable_starAdjoin (Set.countable_range test)).closure
  have hSP : S≤P.toStarSubalgebra := StarSubalgebra.topologicalClosure_minimal
    (StarAlgebra.adjoin_le (by rintro _ ⟨n,rfl⟩; exact (ht n).1)) (VonNeumannCStar.isClosed P)
  have htt (n : ℕ) : test n∈S := StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self n))
  refine ⟨S,hclosed,hsep,hSP,?_⟩
  apply SetLike.ext
  intro A
  rw [NormalGNS.mem_bicommutant]
  constructor
  · intro ha
    have hc := Set.centralizer_subset (Set.centralizer_subset hSP) ha
    change A∈Set.centralizer (Set.centralizer (P : Set (H →L[ℂ] H))) at hc
    change A∈(P : Set (H →L[ℂ] H))
    rwa [VonNeumannAlgebra.centralizer_centralizer] at hc
  · intro hA B hB
    exact (commutes_of_dense_contraction_tests P test hd B
      (fun n => hB _ (htt n)) A hA).eq.symm

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.exists_separable_cstar_bicommutant_oai.{u_1} := @OAI.Kadison.exists_separable_cstar_bicommutant_oai.{u_1}
