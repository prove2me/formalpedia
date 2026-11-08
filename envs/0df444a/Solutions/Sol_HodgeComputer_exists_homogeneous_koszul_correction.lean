-- Prove2me | solution 1 for HodgeComputer.exists_homogeneous_koszul_correction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:19:47.946165+00:00
-- url     : https://prove2.me/submissions/07dfeeda-0e32-4926-9966-33588b13973c

import Definitions.Def_DiamondCertificate
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

noncomputable section

open scoped BigOperators
open RingTheory.Sequence
set_option backward.isDefEq.respectTransparency false

namespace RegularSyzygyAux
variable {R : Type*} [CommRing R]

lemma ofList_ofFn {n : ℕ} (f : Fin n → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  change Ideal.span {x | x ∈ List.ofFn f} = Ideal.span (Set.range f)
  congr 1
  ext x
  exact List.mem_ofFn

lemma syzygy {n : ℕ} (f : Fin n → R)
    (hreg : IsWeaklyRegular R (List.ofFn f))
    (a : Fin n → R) (ha : ∑ i, a i*f i = 0) :
    ∃ U : Fin n → Fin n → R,
      ∀ i, a i = ∑ j, (U i j-U j i)*f j := by
  classical
  induction n with
  | zero => exact ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    let g : Fin n → R := fun i => f i.castSucc
    have hsplit : List.ofFn f = List.ofFn g ++ [f (Fin.last n)] := by
      simpa only [g,List.concat_eq_append] using List.ofFn_succ' f
    rw [hsplit,isWeaklyRegular_append_iff] at hreg
    let J : Ideal R := Ideal.span (Set.range g)
    have hlast : IsSMulRegular (R ⧸ J) (f (Fin.last n)) := by
      have hh := (isWeaklyRegular_singleton_iff _ _).mp hreg.2
      rw [Ideal.smul_eq_mul] at hh
      change IsSMulRegular (R ⧸ (Ideal.ofList (List.ofFn g)*⊤)) _ at hh
      rw [Ideal.mul_top,ofList_ofFn] at hh
      exact hh
    have hprod : f (Fin.last n)*a (Fin.last n) ∈ J := by
      have heq := ha
      rw [Fin.sum_univ_castSucc] at heq
      have he : f (Fin.last n)*a (Fin.last n) =
          -(∑ i : Fin n, a i.castSucc*f i.castSucc) := by
        linear_combination heq
      rw [he]
      apply J.neg_mem
      apply J.sum_mem
      intro i hi
      exact J.mul_mem_left (a i.castSucc) (Ideal.subset_span ⟨i,rfl⟩)
    have hmem : a (Fin.last n) ∈ J :=
      mem_of_isSMulRegular_quotient_of_smul_mem hlast hprod
    obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
    let b : Fin n → R := fun i => a i.castSucc+c i*f (Fin.last n)
    have hb : ∑ i, b i*g i=0 := by
      dsimp only [b]
      simp only [add_mul,Finset.sum_add_distrib]
      have he : (∑ i, c i*f (Fin.last n)*g i) =
          (∑ i, c i*g i)*f (Fin.last n) := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have heq := ha
      rw [Fin.sum_univ_castSucc] at heq
      rw [he,hc]
      exact heq
    obtain ⟨U,hU⟩ := ih g hreg.1 b hb
    let V : Fin (n+1) → Fin (n+1) → R :=
      Fin.snoc (fun i => Fin.snoc (U i) 0) (Fin.snoc c 0)
    refine ⟨V,?_⟩
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [V,Fin.sum_univ_castSucc,g] using hc.symm
    · simp only [Fin.sum_univ_castSucc, V,Fin.snoc_castSucc,Fin.snoc_last,
        zero_sub,neg_mul]
      rw [← hU i]
      dsimp [b]
      ring

end RegularSyzygyAux

open scoped BigOperators
open MvPolynomial RingTheory.Sequence
set_option backward.isDefEq.respectTransparency false
namespace RegularSyzygyAux

variable {R σ : Type*} [CommRing R]

lemma component_mul_homogeneous (P : MvPolynomial σ R) {Q : MvPolynomial σ R}
    {d : ℕ} (hQ : Q.IsHomogeneous d) (r : ℕ) :
    homogeneousComponent (r+d) (P*Q) = homogeneousComponent r P*Q := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial σ R).IsHomogeneous m.degree :=
      isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem (hm.mul hQ),homogeneousComponent_of_mem hm]
    simp only [Nat.add_right_cancel_iff,ite_mul,zero_mul]
  | add P S hP hS => simp only [add_mul,map_add,hP,hS]

lemma homogeneous_syzygy {n d r : ℕ} (f : Fin n → MvPolynomial σ R)
    (hf : ∀ i, (f i).IsHomogeneous d)
    (hreg : IsWeaklyRegular (MvPolynomial σ R) (List.ofFn f))
    (a : Fin n → MvPolynomial σ R) (ha : ∀ i, (a i).IsHomogeneous (r+d))
    (hsum : ∑ i, a i*f i = 0) :
    ∃ U : Fin n → Fin n → MvPolynomial σ R,
      (∀ i j, (U i j).IsHomogeneous r) ∧
      ∀ i, a i = ∑ j, (U i j-U j i)*f j := by
  obtain ⟨V,hV⟩ := syzygy f hreg a hsum
  refine ⟨fun i j => homogeneousComponent r (V i j),?_,?_⟩
  · intro i j
    exact homogeneousComponent_isHomogeneous r (V i j)
  · intro i
    have hh := congrArg (homogeneousComponent (r+d)) (hV i)
    rw [homogeneousComponent_eq_self (ha i),map_sum] at hh
    simpa only [component_mul_homogeneous _ (hf _),map_sub] using hh

end RegularSyzygyAux

open HodgeComputer MvPolynomial RingTheory.Sequence
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace CertificateKoszulAux
variable {n : ℕ}

lemma relation_zero {F : AmbientPoly n} (N M : Fin (n+1) → AmbientPoly n)
    (hlift : directional F N=directional F M) :
    ∑ i, (N i-M i)*pderiv i F=0 := by
  calc
    _ = directional F N-directional F M := by
      simp only [directional,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := sub_eq_zero.mpr hlift

lemma lifts_differ {F : AmbientPoly n}
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F)))
    (N M : Fin (n+1) → AmbientPoly n) (hlift : directional F N=directional F M) :
    ∃ U : Fin (n+1) → Fin (n+1) → AmbientPoly n,
      ∀ i, N i=M i+∑ j, (U i j-U j i)*pderiv j F := by
  have hz := relation_zero N M hlift
  obtain ⟨U,hU⟩ := RegularSyzygyAux.syzygy (fun i => pderiv i F) hreg _ hz
  refine ⟨U,fun i => ?_⟩
  rw [← hU i]
  ring

lemma homogeneous_lifts_differ {F : AmbientPoly n} {d r : ℕ}
    (hF : F.IsHomogeneous d)
    (hreg : IsWeaklyRegular (AmbientPoly n) (List.ofFn (fun i => pderiv i F)))
    (N M : Fin (n+1) → AmbientPoly n)
    (hN : ∀ i, (N i).IsHomogeneous (r+(d-1)))
    (hM : ∀ i, (M i).IsHomogeneous (r+(d-1)))
    (hlift : directional F N=directional F M) :
    ∃ U : Fin (n+1) → Fin (n+1) → AmbientPoly n,
      (∀ i j, (U i j).IsHomogeneous r) ∧
      ∀ i, N i=M i+∑ j, (U i j-U j i)*pderiv j F := by
  have hz := relation_zero N M hlift
  obtain ⟨U,hdeg,hU⟩ := RegularSyzygyAux.homogeneous_syzygy
    (fun i => pderiv i F) (fun _ => hF.pderiv) hreg
    (fun i => N i-M i) (fun i => (hN i).sub (hM i)) hz
  refine ⟨U,hdeg,fun i => ?_⟩
  rw [← hU i]
  ring


end CertificateKoszulAux

theorem solution {n : ℕ} {F : HodgeComputer.AmbientPoly n} {d r : ℕ}
    (hF : F.IsHomogeneous d)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (HodgeComputer.AmbientPoly n)
      (List.ofFn (fun i => MvPolynomial.pderiv i F)))
    (N M : Fin (n+1) → HodgeComputer.AmbientPoly n)
    (hN : ∀ i, (N i).IsHomogeneous (r+(d-1)))
    (hM : ∀ i, (M i).IsHomogeneous (r+(d-1)))
    (hlift : HodgeComputer.directional F N=HodgeComputer.directional F M) :
    ∃ U : Fin (n+1) → Fin (n+1) → HodgeComputer.AmbientPoly n,
      (∀ i j, (U i j).IsHomogeneous r) ∧
      ∀ i, N i=M i+∑ j, (U i j-U j i)*MvPolynomial.pderiv j F :=
  CertificateKoszulAux.homogeneous_lifts_differ hF hreg N M hN hM hlift

#print axioms solution
