-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.Words.moment_limit_of_contractions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:40:48.614254+00:00
-- url     : https://prove2.me/submissions/a5533f3e-9f0f-4748-b512-2b20547114b3

import Mathlib
import Definitions.Def_OAIQ039C035

section
-- module Solutions.OAIQ039_CM.Commutator_WordScaling
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma letter_smul (x : J → A) (c : J → ℂ) (k : K → ℤ) (v : PartialUnitary A) (i : Letter J K) :
    letter (fun j => c j • x j) k v i=c i.1 • letter x k v i := by
  simp only [letter,smul_mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma word_smul (x : J → A) (c : J → ℂ) (k : K → ℤ) (v : PartialUnitary A)
    (l : List (Letter J K)) :
    word (fun j => c j • x j) k v l=(l.map (fun i => c i.1)).prod • word x k v l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [word_cons,letter_smul,ih,List.map_cons,List.prod_cons,
      smul_mul_assoc,mul_smul_comm,smul_smul]
    rw [mul_comm]

omit [StarOrderedRing A] in
lemma moment_limit_of_contractions_oai (τ : A →ₚ[ℂ] ℂ) (k : K → ℤ) (v : ℕ → PartialUnitary A)
    (hlim : ∀ x : J → A,(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
      ∀ l : List (Letter J K),l≠[] → Valid l →
        Tendsto (fun n => τ (word x k (v n) l)) atTop (𝓝 0))
    (x : J → A) (hx : ∀ j,τ (x j)=0)
    (l : List (Letter J K)) (hl : l≠[]) (hv : Valid l) :
    Tendsto (fun n => τ (word x k (v n) l)) atTop (𝓝 0) := by
  let c : J → ℂ := fun j => ((‖x j‖+1 : ℝ):ℂ)
  let y : J → A := fun j => (c j)⁻¹ • x j
  have hc (j : J) : c j≠0 := by
    dsimp [c]
    exact_mod_cast (show ‖x j‖+1≠0 by positivity)
  have hy (j : J) : ‖y j‖≤1 := by
    dsimp [y,c]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
    apply (inv_mul_le_iff₀ (by positivity : 0<‖x j‖+1)).mpr
    linarith
  have hyc (j : J) : τ (y j)=0 := by simp [y,map_smul,hx]
  have he : (fun j => c j • y j)=x := by
    funext j
    simp [y,smul_smul,hc]
  have h := (hlim y hy hyc l hl hv).const_smul ((l.map (fun i => c i.1)).prod)
  have hword (n : ℕ) : τ (word x k (v n) l)=
      ((l.map (fun i => c i.1)).prod) • τ (word y k (v n) l) := by
    rw [←he,word_smul,map_smul]
  simpa only [smul_zero,←hword] using h

end Kadison.FinitePatching.Words

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.FinitePatching.Words.moment_limit_of_contractions_oai.{u_1, u_2, u_3} := @OAI.Kadison.FinitePatching.Words.moment_limit_of_contractions_oai.{u_1, u_2, u_3}
