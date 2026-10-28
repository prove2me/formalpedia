-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.stage_hankel_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:35:59.39642+00:00
-- url     : https://prove2.me/submissions/9a9d9a01-4eeb-4ac6-804c-9252e8d9a38c

import Mathlib
import Definitions.Def_OAIQ039C059
import Definitions.Def_OAIQ039C063
import Theorems.Thm_OAI_Kadison_FreeBlocks_base_block_compression
import Theorems.Thm_OAI_Kadison_FreeBlocks_free_hankel_bound
import Theorems.Thm_OAI_Kadison_FreeBlocks_free_word_structure
import Theorems.Thm_OAI_Kadison_FreeBlocks_propagation_from_stage_all

section
-- module Solutions.OAIQ039_CM.Commutator_CornerSymmetrization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open ContinuousLinearMap MeasureTheory MeasureTheory.Measure

namespace Kadison.CornerSymmetrization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutator_adjoint_norm (G a : H →L[ℂ] H) :
    ‖G.adjoint*a-a*G.adjoint‖=‖G*star a-star a*G‖ := by
  have h : G.adjoint*a-a*G.adjoint = -star (G*star a-star a*G) := by
    simp only [star_sub,star_mul,star_star,neg_sub]
    rfl
  rw [h,norm_neg,norm_star]

end Kadison.CornerSymmetrization

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeStageHankel
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments DihedralCorner

lemma adjoint_commutes_representation {H D : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [CStarAlgebra D]
    (π : D →⋆ₐ[ℂ] (H →L[ℂ] H)) (G : H →L[ℂ] H)
    (h : ∀ a, G.comp (π a)=(π a).comp G) :
    ∀ a, G.adjoint.comp (π a)=(π a).comp G.adjoint := by
  intro a
  have hh : G*π (star a)=π (star a)*G := h (star a)
  have hh' := congrArg star hh
  change G.adjoint*π a=π a*G.adjoint
  simpa only [star_mul,map_star,star_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint] using hh'.symm

lemma adjoint_corner_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : StarSubalgebra ℂ (H →L[ℂ] H)) (p G : H →L[ℂ] H)
    (hp : IsStarProjection p) (ε : ℝ)
    (h : ∀ a : H →L[ℂ] H, a∈M → p*a=a → a*p=a → ‖G.comp a-a.comp G‖≤ε*‖a‖) :
    ∀ a : H →L[ℂ] H, a∈M → p*a=a → a*p=a →
      ‖G.adjoint.comp a-a.comp G.adjoint‖≤ε*‖a‖ := by
  intro a ha hl hr
  have hl' : p*star a=star a := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hr
  have hr' : star a*p=star a := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hl
  change ‖G.adjoint*a-a*G.adjoint‖≤_
  rw [CornerSymmetrization.commutator_adjoint_norm]
  have hh := h (star a) (star_mem ha) hl' hr'
  change ‖G*star a-star a*G‖≤ε*‖star a‖ at hh
  rw [_root_.norm_star a] at hh
  exact hh

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (S : Bool → StarSubalgebra ℂ A)
  (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)
  (hfree : Free S t.functional.toLinearMap)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a, φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer
      (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

variable (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)
  (hGL : ∀ a : D, G.comp (t.functional.gnsStarAlgHom (f a))=
    (t.functional.gnsStarAlgHom (f a)).comp G)
  (hGW : ∀ n u, G.comp
    (innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap =
    (innerRepresentation t htr f S false hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap.comp G)

variable (M : VonNeumannAlgebra t.functional.GNS) (hM : ∀ a : A, t.functional.gnsStarAlgHom a∈M)

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hrot : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

include htr hinc hsize hDgen hgen hGL hGW hM hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD in
theorem stage_hankel_bound_oai {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n : ℕ) (q : Matrix (I n) (I n) ℂ) (hq : IsStarProjection q)
    (α : ℝ) (hα : 0<α) (hατ : factorTrace t f hf (φ n q)=(α:ℂ))
    (w : κ → D)
    (hcol : ∀ i j, star (w i)*w j=if i=j then φ n q else 0)
    (hinit : ∀ i, φ n q*star (w i)=star (w i))
    (htotal : ∑ i, w i*star (w i)=1)
    (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (ε : ℝ) (hε : 0≤ε)
    (hsmallq : ∀ a : t.functional.GNS →L[ℂ] t.functional.GNS, a∈M →
      t.functional.gnsStarAlgHom (f (φ n q))*a=a →
      a*t.functional.gnsStarAlgHom (f (φ n q))=a → ‖G.comp a-a.comp G‖≤ε*‖a‖)
    (hsmalle : ∀ a : A, (e:A)*a*(e:A)=a →
      ‖G*t.functional.gnsStarAlgHom a-t.functional.gnsStarAlgHom a*G‖≤ε*‖a‖) :
    ‖(ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
      (baseEmbedding t S hfree).toContinuousLinearMap).comp
      ((G*t.functional.gnsStarAlgHom (s:A)-t.functional.gnsStarAlgHom (s:A)*G).comp
        (baseEmbedding t S hfree).toContinuousLinearMap)‖≤1040*ε := by
  obtain ⟨B,hBn,hB,hB'⟩ := free_word_structure t htr f hf S false true hS hfree hgen
    Bool.false_ne_true (fun b => by cases b <;> simp) I φ inc hinc hsize hDgen G hGL hGW
  have hb : ∀ k a (x : letterSpace t S false) v,
      G (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k v)=
        repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k (B k v) := by
    intro k a x v
    exact hB k _ _ v
  have hb' : ∀ k a (x : letterSpace t S false) v,
      G.adjoint (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k v)=
        repeatedOutput t S f hf hS hfree Bool.false_ne_true a x k ((B k).adjoint v) := by
    intro k a x v
    exact hB' k _ _ v
  let sl := letterOf t S true (s:A) hs hs0
  have sn : ‖sl‖=1 := norm_letterOf_unitary t S true s hs hs0
  have hg' := adjoint_commutes_representation (t.functional.gnsStarAlgHom.comp f) G hGL
  have hpq : IsStarProjection (t.functional.gnsStarAlgHom (f (φ n q))) :=
    ((hq.map (φ n)).map f).map t.functional.gnsStarAlgHom
  have hsmallq' := adjoint_corner_bound M.toStarSubalgebra _ G hpq ε hsmallq
  have hprop := propagation_from_stage_all t htr S f hf hS hfree Bool.false_ne_true
    I φ inc hinc hsize hDgen hgen G B hb hGL M hM sl sn n q hq α hα hατ w hcol
    hinit htotal ε hε hsmallq
  have hprop' := propagation_from_stage_all t htr S f hf hS hfree Bool.false_ne_true
    I φ inc hinc hsize hDgen hgen G.adjoint (fun k => (B k).adjoint) hb' hg' M hM
    sl sn n q hq α hα hατ w hcol hinit htotal ε hε hsmallq'
  have hbnd := free_hankel_bound t S hfree f hf hS htr d s hd hs hd0 hs0 hrot hd2 hs2
    hp hpform hpd hdp hpD G B hb hb' e0 e heq heproj he hr 16 ε (by norm_num) hε
    hsmalle (by simpa only [show (2:ℝ)*16=32 by norm_num] using hprop)
      (by simpa only [show (2:ℝ)*16=32 by norm_num] using hprop')
  rw [base_block_compression t S f hf hS hfree G _ B hb hb' sl sn]
  change ‖B 0*baseAction t S hfree (s:A)-baseAction t S hfree (s:A)*B 0‖≤1040*ε
  simpa only [show (16:ℝ)*(1+4*16)=1040 by norm_num] using hbnd

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.FreeBlocks.stage_hankel_bound_oai.{u_1, u_2} := @OAI.Kadison.FreeBlocks.stage_hankel_bound_oai.{u_1, u_2}
