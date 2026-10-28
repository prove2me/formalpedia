-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.exists_finite_word_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:52:18.539108+00:00
-- url     : https://prove2.me/submissions/3dc1f967-50d1-4077-a02b-f00374e92826

import Mathlib
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_CornerPhase_exists_relative_corner_phase
import Theorems.Thm_OAI_Kadison_RelativeCornerQuantization_exists_relative_centered_compression

section
-- module Solutions.OAIQ039_CM.Commutator_CornerCenteredEstimates
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

open TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

omit [StarOrderedRing A] in
lemma cornerCenter_left {p : A} (hp : IsStarProjection p) (b : A) :
    p*cornerCenter τ p b=cornerCenter τ p b := by
  simp only [cornerCenter,mul_sub,mul_smul_comm,←mul_assoc,hp.isIdempotentElem.eq]

omit [StarOrderedRing A] in
lemma cornerCenter_right {p : A} (hp : IsStarProjection p) (b : A) :
    cornerCenter τ p b*p=cornerCenter τ p b := by
  simp only [cornerCenter,sub_mul,smul_mul_assoc,mul_assoc,hp.isIdempotentElem.eq]

include hτ in
omit [StarOrderedRing A] in
lemma cornerCenter_trace {p : A} (hp : IsStarProjection p) (ht : 0<(τ p).re) (b : A) :
    τ (cornerCenter τ p b)=0 := by
  have ht0 : τ p≠0 := fun h => by rw [h,Complex.zero_re] at ht; exact lt_irrefl _ ht
  have he : τ (p*b*p)=τ (p*b) := by rw [hτ (p*b),←mul_assoc,hp.isIdempotentElem.eq]
  simp only [cornerCenter,map_sub,map_smul,smul_eq_mul,cornerScalar,he]
  rw [div_mul_cancel₀ _ ht0,sub_self]

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Continuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma trace_star (a : A) : τ (star a)=star (τ a) := by
  have h := inner_conj_symm (𝕜:=ℂ) (τ.toPreGNS a) (τ.toPreGNS 1)
  change star (τ (star (1:A)*a))=τ (star a*1) at h
  simpa only [star_one,one_mul,mul_one] using h.symm

lemma norm_trace_star (a : A) : ‖τ (star a)‖=‖τ a‖ := by
  rw [trace_star,_root_.norm_star]

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma norm_trace_star_mul (a b : A) : ‖τ (star a*b)‖=‖τ (a*star b)‖ := by
  rw [←norm_trace_star τ (star a*b),star_mul,star_star,hτ]

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RelativeCornerPhase
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.CornerPhase

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M N : VonNeumannAlgebra H) (hNM : N ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ hNM in
theorem exists_relative_signed_phase {J : Type*} [Fintype J]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (hN : DiffuseProjection.HasNoMinimalProjections N)
    (q : M) (hq : IsStarProjection q) (hqN : (q : H →L[ℂ] H)∈N)
    (hqt : 0<(τ q).re)
    (a : J → M) (k : J → ℤ) (hk : ∀ j,k j≠0) {ε : ℝ} (hε : 0<ε) :
    ∃ u : FinitePatching.PartialUnitary M, u.support=q ∧
      (∀ j, ‖τ (u.power (k j)*a j)‖<ε*(τ q).re) ∧ (u.val : H →L[ℂ] H)∈N := by
  let b : J → M := fun j => match k j with
    | .ofNat _ => a j
    | .negSucc _ => star (a j)
  obtain ⟨u,h1,h2,h3,h4,_,hu,hmem⟩ := exists_relative_corner_phase M N hNM τ hτ
    hnormal hfaith hN q hq hqN hqt b (fun j => (k j).natAbs)
    (fun j => Int.natAbs_pos.mpr (hk j)) hε
  let v : FinitePatching.PartialUnitary M := ⟨u,q,hq,h1,h2,h3,h4⟩
  refine ⟨v,rfl,?_,hmem⟩
  intro j
  have hj := hu j
  cases he : k j with
  | ofNat n =>
    cases n with
    | zero => exact (hk j he).elim
    | succ n =>
      change ‖τ (u^(n+1)*a j)‖<ε*(τ q).re
      simpa only [b,he,Int.natAbs_ofNat',Int.natAbs_negSucc] using hj
  | negSucc n =>
    change ‖τ ((star u)^(n+1)*a j)‖<ε*(τ q).re
    rw [←star_pow,TracialL2.norm_trace_star_mul τ hτ]
    simpa only [b,he,Int.natAbs_ofNat',Int.natAbs_negSucc] using hj

end Kadison.CornerPhase

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteWordPatchProducer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
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

namespace Kadison.FinitePatching

open Words

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hRM hτ hmono in
theorem exists_finite_word_patch_oai {J K : Type*} [Fintype J] [Fintype K]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (x : J → M) (k : K → ℤ) (hk : ∀ i,k i≠0)
    (v : PartialUnitary M) (hvR : (v.support : H →L[ℂ] H)∈R)
    (hrest : 0<(τ (1-v.support)).re) (N : ℕ) {δ ζ : ℝ} (hδ : 0<δ) (hζ : 0<ζ) :
    ∃ w : PartialUnitary M, (w.val : H →L[ℂ] H)∈R ∧
      (w.support : H →L[ℂ] H)∈R ∧ w.support ≤ 1-v.support ∧
      v.support*w.support=0 ∧ 0<(τ w.support).re ∧ (τ w.support).re<ζ ∧
      (∀ i,‖τ (w.power (k i))‖ ≤ δ*(τ w.support).re) ∧
      (∀ (s : List (Letter J K)) (j : J),s.length ≤ N →
        TracialL2.norm τ (w.support*cornerCenter τ (1-v.support)
          (word x k v s*x j)*w.support)^2 ≤ δ^2*(τ w.support).re) ∧
      (∀ (s t : List (Letter J K)) (j : J) (i : K),s.length ≤ N → t.length ≤ N →
        ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ δ*(τ w.support).re) := by
  classical
  let L := SmallList (Letter J K) N
  let c : L×J → M := fun a => cornerCenter τ (1-v.support) (word x k v a.1.val*x a.2)
  have hpR : ((1-v.support:M) : H →L[ℂ] H)∈R := R.sub_mem R.one_mem hvR
  obtain ⟨q,hqR,hq,hqp,hqt,hqζ,hsmall⟩ :=
    RelativeCornerQuantization.exists_relative_centered_compression M τ hτ stage hmono
      hnormal hfaith hone hirr hgrow R hstage (1-v.support) hpR v.projection.one_sub hrest
      c (fun a => cornerCenter_trace τ hτ v.projection.one_sub hrest _)
      (fun a => cornerCenter_left τ v.projection.one_sub _)
      (fun a => cornerCenter_right τ v.projection.one_sub _) hδ hζ
  let a : Option (L×L×J)×K → M := fun i => match i.1 with
    | none => 1
    | some t => word x k v t.2.1.val*word x k v t.1.val*x t.2.2
  obtain ⟨w,hwq,hphase,hwR⟩ := CornerPhase.exists_relative_signed_phase M R hRM τ hτ
    hnormal hfaith hdiffuse q hq hqR hqt a (fun i => k i.2) (fun i => hk i.2) hδ
  have horth : v.support*w.support=0 := by
    rw [hwq]
    have hh := (hq.le_iff_mul_eq_right v.projection.one_sub).mp hqp
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  refine ⟨w,hwR,by simpa only [hwq] using hqR,by simpa only [hwq] using hqp,
    horth,by simpa only [hwq] using hqt,by simpa only [hwq] using hqζ,?_,?_,?_⟩
  · intro i
    have hh := (hphase (none,i)).le
    simpa only [a,mul_one,hwq] using hh
  · intro s j hs
    have hh := (hsmall (smallList (Letter J K) s hs,j)).le
    simpa only [c,smallList,hwq] using hh
  · intro s t j i hs ht
    have hh := (hphase (some (smallList (Letter J K) s hs,smallList (Letter J K) t ht,j),i)).le
    simpa only [a,smallList,hwq] using hh

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.FinitePatching.exists_finite_word_patch_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.FinitePatching.exists_finite_word_patch_oai.{u_1, u_2, u_3, u_4}
