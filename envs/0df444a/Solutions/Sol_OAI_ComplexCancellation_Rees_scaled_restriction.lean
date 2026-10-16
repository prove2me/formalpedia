-- Prove2me | solution 1 for OAI.ComplexCancellation.Rees.scaled_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:56:15.27178+00:00
-- url     : https://prove2.me/submissions/42037a21-6c46-46c7-a710-c616b5e0705f

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ReesDerivation.lean:L75-L96
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Rees.scaled_restriction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Theorems.Thm_OAI_ComplexCancellation_LND_cancel_factor_locallyNilpotent
import Theorems.Thm_OAI_ComplexCancellation_LaurentDerivation_locallyNilpotent

-- ---- from OAI.Algebra.AffineCancellation.FactorDerivation ----
namespace OAI

noncomputable section

namespace ComplexCancellation.FactorDerivation
variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [IsDomain R]
  [Algebra k S] [Algebra k R]
variable (f : S →ₐ[k] R) (hf : Function.Injective f)
  (D : Derivation k R R) (c : R) (hc : c ≠ 0)
  (h : ∀ s : S, ∃ t : S, D (f s)=c*f t)
lemma apply_spec (s : S) : D (f s)=c*f (derivation f hf D c hc h s) := specification f D c h s
end ComplexCancellation.FactorDerivation

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Primitive ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LND
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
omit [CharZero k] [IsDomain R] in
lemma iterate_replica (D : Derivation k R R) (c : R) (hc : D c=0) (r : R) (n : ℕ) :
    ((c • D : Derivation k R R) : R → R)^[n] r=c^n*(D : R → R)^[n] r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,Derivation.smul_apply,Derivation.leibniz,
      Derivation.leibniz_pow,hc]
    simp only [smul_eq_mul]
    rw [pow_succ,Function.iterate_succ_apply']
    ring

omit [CharZero k] [IsDomain R] in
lemma replica (D : Derivation k R R) (hD : LocallyNilpotent D) (c : R) (hc : D c=0) :
    LocallyNilpotent (c • D) := by
  intro r
  obtain ⟨n,hn⟩ := hD r
  exact ⟨n,by rw [iterate_replica D c hc,hn,mul_zero]⟩

end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.ReesClearing ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
lemma embedding_q : embedding q=T 1 := by simp [q,eval,values]
lemma clear_coefficient (r : A) : c r ∈ Clearing.subalgebra embedding q := by
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ r
  change c (aπ r) ∈ _
  induction r using MvPolynomial.induction_on with
  | C z =>
    refine ⟨0,algebraMap ℂ B z,?_⟩
    rw [pow_zero,one_mul]
    have ha : aπ (MvPolynomial.C z)=algebraMap ℂ A z := aπ.commutes z
    rw [ha,c.commutes,embedding.commutes]
  | add r s hr hs => rw [map_add,map_add]; exact add_mem hr hs
  | mul_X r i hr =>
    rw [map_mul,map_mul]
    apply mul_mem hr
    fin_cases i
    · refine ⟨0,q*π (X 1),?_⟩
      simp only [pow_zero,one_mul,map_mul,embedding_q,embedding_π,eval,aeval_X,
        values,Matrix.cons_val_zero,Matrix.cons_val_one,a]
      change c (aπ (X 0))=T 1*(c (aπ (X 0))*T (-1))
      rw [mul_left_comm (T 1 : L),← T_add]
      norm_num
    · refine ⟨0,π (X 2),?_⟩
      simp only [pow_zero,one_mul,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      rfl
    · refine ⟨0,π (X 3),?_⟩
      simp only [pow_zero,one_mul,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      rfl
    · refine ⟨2,π (X 4),?_⟩
      simp only [embedding_q,T_pow,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      change T 2*c (aπ (X 3))=c (aπ (X 3))*T 2
      exact mul_comm (T 2 : L) (c (aπ (X 3)))
    · refine ⟨2,π (X 5),?_⟩
      simp only [embedding_q,T_pow,embedding_π,eval,aeval_X,values,Matrix.cons_val,a]
      change T 2*c (aπ (X 4))=c (aπ (X 4))*T 2
      exact mul_comm (T 2 : L) (c (aπ (X 4)))

lemma clear_T (n : ℤ) : (T n : L) ∈ Clearing.subalgebra embedding q := by
  obtain ⟨m,hm⟩ : ∃ m : ℕ, 0 ≤ (m : ℤ)+n := ⟨n.natAbs,by omega⟩
  refine ⟨m,q^((m : ℤ)+n).toNat,?_⟩
  rw [map_pow,embedding_q,T_pow,T_pow,← T_add]
  congr 1
  simp only [mul_one,Int.toNat_of_nonneg hm]
lemma clear_all (r : L) : ∃ n : ℕ, ∃ s : B, embedding q^n*r=embedding s := by
  change r ∈ Clearing.subalgebra embedding q
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => exact add_mem hr hs
  | C_mul_T n r => exact mul_mem (clear_coefficient r) (clear_T n)
end ComplexCancellation.Rees

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.ReesDerivation ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
lemma uniform_clear (f : Fin 6 → L) :
    ∃ n : ℕ, ∀ i, ∃ b : B, embedding q^n*f i=embedding b := by
  classical
  choose n b hb using fun i => clear_all (f i)
  refine ⟨∑ i, n i, fun i => ⟨q^((∑ j,n j)-n i)*b i,?_⟩⟩
  have hi : n i ≤ ∑ j, n j := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  rw [map_mul,map_pow,← hb,← mul_assoc,← pow_add,Nat.sub_add_cancel hi]
lemma stable_of_generators (E : Derivation ℂ L L)
    (h : ∀ i : Fin 6, ∃ t : B, E (embedding (π (X i)))=embedding t) :
    ∀ b : B, ∃ t : B, E (embedding b)=embedding t := by
  intro b
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ b
  change ∃ t, E (embedding (π r))=embedding t
  induction r using MvPolynomial.induction_on with
  | C z => exact ⟨0,by simp only [MvPolynomial.C_eq_algebraMap,AlgHom.commutes,
      Derivation.map_algebraMap,map_zero]⟩
  | add r s hr hs =>
    obtain ⟨r',hr'⟩ := hr
    obtain ⟨s',hs'⟩ := hs
    exact ⟨r'+s',by rw [map_add,map_add,map_add,hr',hs',map_add]⟩
  | mul_X r i hr =>
    obtain ⟨r',hr'⟩ := hr
    obtain ⟨s',hs'⟩ := h i
    refine ⟨π r*s'+π (X i)*r',?_⟩
    rw [map_mul,map_mul,Derivation.leibniz,hr',hs',smul_eq_mul,smul_eq_mul,
      map_add,map_mul,map_mul]
lemma clear_annihilate (D : Derivation ℂ A A) (n : ℕ)
    (h : ∀ b : B, embedding q^n * LaurentDerivation.extension D (embedding b)=0) : D=0 := by
  let D' := LaurentDerivation.extension D
  have hq : D' (embedding q)=0 := by rw [embedding_q]; exact LaurentDerivation.extension_T D 1
  have hnon : embedding q^n ≠ 0 := pow_ne_zero n (by rw [embedding_q]; exact (isUnit_T _).ne_zero)
  ext a
  obtain ⟨m,b,hb⟩ := clear_all (c a)
  have hd : D' (embedding b)=0 := (mul_eq_zero.mp (h b)).resolve_left hnon
  have he := congrArg D' hb
  rw [Derivation.leibniz,Derivation.leibniz_pow,hq,smul_zero,smul_zero,smul_zero,add_zero,hd] at he
  have ha : D' (c a)=0 := (smul_eq_zero.mp he).resolve_left (pow_ne_zero m (by rw [embedding_q]; exact (isUnit_T _).ne_zero))
  change LaurentDerivation.extension D (LaurentPolynomial.C a)=0 at ha
  rw [LaurentDerivation.extension_C] at ha
  have hz := congrArg (fun t : L => t.coeff 0) ha
  simpa [LaurentPolynomial.C_apply] using hz
lemma scaled_is_ln (D : Derivation ℂ A A) (hD : LND.LocallyNilpotent D) (n : ℕ) :
    LND.LocallyNilpotent (k := ℂ) (R := L) (embedding q^n • LaurentDerivation.extension D) := by
  apply LND.replica _ (LaurentDerivation.locallyNilpotent D hD)
  rw [Derivation.leibniz_pow,embedding_q,LaurentDerivation.extension_T,smul_zero,smul_zero]
lemma scaled_fixes (D : Derivation ℂ A A) (r : A) (hDr : D r=0) (i : ℤ) (s : B)
    (hs : embedding s=T i*c r) (n : ℕ) :
    (embedding q^n • LaurentDerivation.extension D) (embedding s)=0 := by
  have he : LaurentDerivation.extension D (embedding s)=0 := by
    rw [hs,Derivation.leibniz]
    have hr : LaurentDerivation.extension D (c r)=0 := by
      change LaurentDerivation.extension D (LaurentPolynomial.C r)=0
      rw [LaurentDerivation.extension_C,hDr,map_zero]
    rw [hr,LaurentDerivation.extension_T,smul_zero,smul_zero,add_zero]
  exact (congrArg (fun z : L => embedding q^n*z) he).trans (mul_zero _)

lemma restrict_stable (E' : Derivation ℂ L L) (hE' : LND.LocallyNilpotent (k := ℂ) (R := L) E')
    (hstable : ∀ b : B, ∃ t : B, E' (embedding b)=embedding t) :
    ∃ E : Derivation ℂ B B, LND.LocallyNilpotent E ∧ ∀ b, E' (embedding b)=embedding (E b) := by
  have hfac : ∀ b : B, ∃ t : B, E' (embedding b)=1*embedding t := by simpa only [one_mul] using hstable
  let E := FactorDerivation.derivation (k := ℂ) (R := L) embedding embedding_injective E' 1 one_ne_zero hfac
  have hspec (b : B) : E' (embedding b)=embedding (E b) := by
    simpa only [one_mul] using FactorDerivation.apply_spec (k := ℂ) (R := L) embedding embedding_injective E' 1 one_ne_zero hfac b
  exact ⟨E,LND.cancel_factor_locallyNilpotent (k := ℂ) (R := L) embedding embedding_injective E' hE' E one_ne_zero (by simpa only [one_mul] using hspec),hspec⟩
lemma scaled_restriction (D : Derivation ℂ A A) (hD : LND.LocallyNilpotent D)
    (hDn : D ≠ 0) (r : A) (hDr : D r=0) (i : ℤ) (s : B)
    (hs : embedding s=T i*c r) :
    ∃ E : Derivation ℂ B B, LND.LocallyNilpotent E ∧ E ≠ 0 ∧ E q=0 ∧ E s=0 := by
  obtain ⟨n,hn⟩ := uniform_clear (fun i => LaurentDerivation.extension D (embedding (π (X i))))
  let E' := embedding q^n • LaurentDerivation.extension D
  have hgen (i : Fin 6) : ∃ t : B, E' (embedding (π (X i)))=embedding t := hn i
  obtain ⟨E,hE,hspec⟩ := restrict_stable E' (scaled_is_ln D hD n) (stable_of_generators E' hgen)
  refine ⟨E,hE,?_,?_,?_⟩
  · intro hz
    apply hDn
    apply clear_annihilate D n
    intro b
    change E' (embedding b)=0
    rw [hspec,hz,Derivation.zero_apply,map_zero]
  · apply embedding_injective
    rw [map_zero,← hspec]
    change embedding q^n*LaurentDerivation.extension D (embedding q)=0
    rw [embedding_q,LaurentDerivation.extension_T,mul_zero]
  · apply embedding_injective
    rw [map_zero,← hspec]
    exact scaled_fixes D r hDr i s hs n

end ComplexCancellation.Rees

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Rees.scaled_restriction := @_root_.OAI.ComplexCancellation.Rees.scaled_restriction
