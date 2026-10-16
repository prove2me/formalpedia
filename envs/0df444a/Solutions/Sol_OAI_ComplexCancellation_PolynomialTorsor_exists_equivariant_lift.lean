-- Prove2me | solution 1 for OAI.ComplexCancellation.PolynomialTorsor.exists_equivariant_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:46:30.916039+00:00
-- url     : https://prove2.me/submissions/5189a397-969e-4895-9eb3-9b9d5d0c6b83

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/EquivariantLift.lean:L10-L49
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.PolynomialTorsor.exists_equivariant_lift. The node keeps its source
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
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse
import Definitions.Def_OAI_Algebra_AffineCancellation_ReplicaLift
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentEuler
import Definitions.Def_OAI_Algebra_AffineCancellation_Intertwining
import Theorems.Thm_OAI_ComplexCancellation_BezoutFrame_exists_frame
import Theorems.Thm_OAI_ComplexCancellation_LND_cancel_factor_locallyNilpotent
import Theorems.Thm_OAI_ComplexCancellation_LaurentDerivation_locallyNilpotent
import Theorems.Thm_OAI_ComplexCancellation_RationalSlice_constant_fraction
import Theorems.Thm_OAI_ComplexCancellation_RelativeClearing_uniform
import Theorems.Thm_OAI_ComplexCancellation_Torsor_forward_pullback
import Theorems.Thm_OAI_ComplexCancellation_Torsor_frameMap_intertwining

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

-- ---- from OAI.Algebra.AffineCancellation.RelativeClearing ----
namespace OAI

noncomputable section

namespace ComplexCancellation.RelativeClearing
variable {k A B R : Type*} [CommRing k] [CommRing A] [IsDomain A] [CommRing B] [CommRing R]
  [Algebra k A] [Algebra k B] [Algebra k R]
variable (h : A →ₐ[k] B) (f : B →ₐ[k] R) (D : Derivation k A A)
lemma image_mem (b : B) : f b ∈ subalgebra h f D := ⟨1,b,D.map_one_eq_zero,one_ne_zero,by simp⟩
end ComplexCancellation.RelativeClearing

namespace ComplexCancellation.DerivationRange
variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R] [Algebra k B] [Algebra k R]
lemma stable_of_generators (f : B →ₐ[k] R) (E : Derivation k R R) (s : Set B)
    (hs : Algebra.adjoin k s=⊤) (he : ∀ b∈s, ∃ t, E (f b)=f t) : ∀ b, ∃ t, E (f b)=f t := by
  have h : Algebra.adjoin k s ≤ stable f E := Algebra.adjoin_le he
  rw [hs] at h
  exact fun b => h (show b∈(⊤ : Subalgebra k B) from trivial)
end ComplexCancellation.DerivationRange

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.InvariantRestriction ----
namespace OAI

noncomputable section

namespace ComplexCancellation.InvariantRestriction
variable {k A B R : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A]
  [CommRing B] [CommRing R] [IsDomain R] [Algebra k A] [Algebra k B] [Algebra k R]
lemma stable_restrict (f : B →ₐ[k] R) (hf : Function.Injective f) (E : Derivation k R R)
    (hE : LND.LocallyNilpotent E) (hs : ∀ b, ∃ t, E (f b)=f t) :
    ∃ D : Derivation k B B, LND.LocallyNilpotent D ∧ ∀ b, E (f b)=f (D b) := by
  have he : ∀ b, ∃ t, E (f b)=1*f t := by simpa only [one_mul] using hs
  let D := FactorDerivation.derivation f hf E 1 one_ne_zero he
  have hspec (b : B) : E (f b)=f (D b) := by
    simpa only [one_mul] using FactorDerivation.apply_spec f hf E 1 one_ne_zero he b
  exact ⟨D,LND.cancel_factor_locallyNilpotent f hf E hE D one_ne_zero (by simpa only [one_mul] using hspec),hspec⟩
lemma exists_restriction [Algebra.FiniteType k B]
    (h : A →ₐ[k] B) (f : B →ₐ[k] R) (hf : Function.Injective f)
    (D : Derivation k A A) (E : Derivation k R R) (hE : LND.LocallyNilpotent E)
    (he : ∀ a, E (f (h a))=f (h (D a)))
    (hc : ∀ r, r ∈ RelativeClearing.subalgebra h f D) :
    ∃ c : A, ∃ E' : Derivation k B B, D c=0 ∧ c≠0 ∧ LND.LocallyNilpotent E' ∧
      ∀ b, f (E' b)=f (h c)*E (f b) := by
  obtain ⟨s,hs⟩ := Algebra.FiniteType.out (R := k) (A := B)
  obtain ⟨c,hDc,hcn,hgen⟩ := RelativeClearing.uniform h f D s E (fun _ => hc _)
  let E₀ := f (h c) • E
  have hE₀ : LND.LocallyNilpotent E₀ := LND.replica E hE _ (by rw [he,hDc,map_zero,map_zero])
  have hstable : ∀ b, ∃ t, E₀ (f b)=f t :=
    DerivationRange.stable_of_generators f E₀ (s : Set B) hs hgen
  obtain ⟨E',hE',hspec⟩ := stable_restrict f hf E₀ hE₀ hstable
  exact ⟨c,E',hDc,hcn,hE',fun b => (hspec b).symm⟩
end ComplexCancellation.InvariantRestriction

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.RationalSlice ----
namespace OAI

noncomputable section

namespace ComplexCancellation.RationalSlice
open DifferentialSlice FractionDerivation
variable {k R K : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [Algebra k R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Algebra k K] [IsScalarTower k R K]

omit [IsDomain R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Algebra k K] [IsScalarTower k R K] [CharZero k] in
lemma last_nonzero (D : Derivation k R R) {r : R} (hr : r ≠ 0)
    (h : ∃ m : ℕ, (D : R → R)^[m] r = 0) :
    ∃ n : ℕ, (D : R → R)^[n] r ≠ 0 ∧ D ((D : R → R)^[n] r) = 0 := by
  obtain ⟨m, hm⟩ := h
  induction m generalizing r with
  | zero => exact (hr hm).elim
  | succ m ih =>
    by_cases hdr : D r = 0
    · exact ⟨0, hr, hdr⟩
    · rw [Function.iterate_succ_apply] at hm
      obtain ⟨n, hn, hdn⟩ := ih hdr hm
      exact ⟨n+1, by simpa only [Function.iterate_succ_apply] using hn,
        by simpa only [Function.iterate_succ_apply] using hdn⟩

end ComplexCancellation.RationalSlice

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.PolynomialSlice ----
namespace OAI

noncomputable section

namespace ComplexCancellation.DifferentialSlice
variable {k K : Type*} [CommRing k] [Field K] [CharZero K] [Algebra k K]
end ComplexCancellation.DifferentialSlice

namespace ComplexCancellation.InvariantClearing
variable {k R S : Type*} [CommRing k] [CommRing R] [IsDomain R] [CommRing S]
  [Algebra k R] [Algebra k S]
end ComplexCancellation.InvariantClearing

namespace ComplexCancellation.PolynomialModel
open Polynomial DifferentialSlice FractionDerivation
variable {k R : Type*} [Field k] [CommRing R] [IsDomain R] [CharZero R] [Algebra k R]
variable (D : Derivation k R R) (hD : LND.LocallyNilpotent D)
include hD in
omit [IsDomain R] [CharZero R] in
lemma local_slice (hn : D ≠ 0) : ∃ s : R, D s ≠ 0 ∧ D (D s)=0 := by
  obtain ⟨r,hr⟩ : ∃ r, D r ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    ext r
    exact h r
  obtain ⟨n,hn,hdn⟩ := RationalSlice.last_nonzero D hr (hD (D r))
  refine ⟨(D : R → R)^[n] r,?_,?_⟩
  · simpa only [← Function.iterate_succ_apply',Function.iterate_succ_apply] using hn
  · simpa only [← Function.iterate_succ_apply',Function.iterate_succ_apply] using hdn
variable {t : K (R := R)} (ht : extend D t=1)
lemma evaluation_model (r : R) : evaluation (D := D) (t := t) (model D hD ht r)=ι (k := k) r :=
  Classical.choose_spec (exists_model D hD ht r)
lemma model_injective : Function.Injective (model D hD ht) := by
  intro r s he
  have hi : Function.Injective (ι (k := k) (R := R)) := IsFractionRing.injective R (K (R := R))
  apply hi
  have h := congrArg (evaluation (D := D) (t := t)) he
  simpa only [evaluation_model] using h
lemma derivative_model (r : R) : (model D hD ht r).derivative=model D hD ht (D r) := by
  apply evaluation_injective D ht
  change aeval t (model D hD ht r).derivative = evaluation (D := D) (t := t) _
  rw [← derivative_eval _ ht]
  change extend D (evaluation (D := D) (t := t) (model D hD ht r)) = evaluation (D := D) (t := t) _
  rw [evaluation_model,evaluation_model]
  exact extend_algebraMap D r
lemma clear_constant (c : F D) : C c ∈ InvariantClearing.subalgebra (model D hD ht) D := by
  obtain ⟨a,b,ha,hb,hbn,hab⟩ := RationalSlice.constant_fraction D hD c.property
  refine ⟨b,a,hb,hbn,?_⟩
  apply evaluation_injective D ht
  rw [map_mul,evaluation_model,evaluation_model]
  simp only [evaluation,AlgHom.restrictScalars_apply,Polynomial.aeval_C]
  change ι (k := k) b*(c : K (R := R))=ι (k := k) a
  have hn : ι (k := k) b ≠ 0 := by
    have hi : Function.Injective (ι (k := k) (R := R)) := IsFractionRing.injective R (K (R := R))
    simpa only [map_zero] using hi.ne hbn
  change ι (k := k) a/ι (k := k) b=(c : K (R := R)) at hab
  rw [← hab,← mul_div_assoc,mul_div_cancel_left₀ _ hn]
lemma clear_X (s : R) (hs : D s ≠ 0) (he : D (D s)=0)
    (hsl : t=ι (k := k) s/ι (k := k) (D s)) :
    X ∈ InvariantClearing.subalgebra (model D hD ht) D := by
  refine ⟨D s,s,he,hs,?_⟩
  apply evaluation_injective D ht
  rw [map_mul,evaluation_model,evaluation_model]
  simp only [evaluation,AlgHom.restrictScalars_apply,Polynomial.aeval_X]

  rw [hsl,← mul_div_assoc]
  apply mul_div_cancel_left₀
  have hi : Function.Injective (ι (k := k) (R := R)) := IsFractionRing.injective R (K (R := R))
  simpa only [map_zero] using hi.ne hs
lemma clear_polynomial (s : R) (hs : D s ≠ 0) (he : D (D s)=0)
    (hsl : t=ι (k := k) s/ι (k := k) (D s)) (p : Polynomial (F D)) :
    p ∈ InvariantClearing.subalgebra (model D hD ht) D := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact add_mem hp hq
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    exact mul_mem (clear_constant D hD ht c) (pow_mem (clear_X D hD ht s hs he hsl) n)
end ComplexCancellation.PolynomialModel

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.TorsorFrame ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
open MvPolynomial (X aeval aeval_X eval₂Hom_C eval₂Hom_X)
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P)
variable (Q : Frame ρ)
lemma base_p_ne_zero (hρ : Function.Injective ρ) : base ρ Degeneration.p ≠ 0 := by
  have hp : Degeneration.p ≠ 0 := Degeneration.p_regular.ne_zero
  change C (ρ Degeneration.p) ≠ 0
  intro hz
  have hn : ρ Degeneration.p ≠ 0 := by simpa only [map_zero] using hρ.ne hp
  apply hn
  have he := congrArg (fun z : L (P := P) => z.coeff 0) hz
  simpa [LaurentPolynomial.C_apply] using he
variable [IsDomain P]
end ComplexCancellation.Torsor

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.TorsorInverse ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ)
variable (f : P →ₐ[ℂ] KB) (hf : f.comp ρ=ib.comp Bundle.pullback)
include hf
lemma back_a : f Q.a₀*w ρ Q f=bc Determinant.a := by
  dsimp [w]
  calc _ = (f Q.a₀*f Q.c₀)*bc Determinant.a-(f Q.a₀*f Q.b₀)*bc Determinant.d := by ring
    _ = _ := by rw [back_ac ρ Q f hf,back_ab ρ Q f hf]; linear_combination bc Determinant.a*bc_det
lemma back_d : f Q.d₀*w ρ Q f=bc Determinant.d := by
  dsimp [w]
  calc _ = (f Q.d₀*f Q.c₀)*bc Determinant.a-(f Q.d₀*f Q.b₀)*bc Determinant.d := by ring
    _ = _ := by rw [back_dc ρ Q f hf,back_db ρ Q f hf]; linear_combination bc Determinant.d*bc_det
lemma backward_frameMap : (backward ρ Q f hf).comp (frameMap ρ Q)=bc := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change backward ρ Q f hf (frameMap ρ Q Determinant.a)=bc Determinant.a
    rw [frameMap_a,map_mul,backward_C,backward_T_one,back_a ρ Q f hf]
  · change backward ρ Q f hf (frameMap ρ Q Determinant.d)=bc Determinant.d
    rw [frameMap_d,map_mul,backward_C,backward_T_one,back_d ρ Q f hf]
  · change backward ρ Q f hf (frameMap ρ Q Determinant.b)=bc Determinant.b
    rw [frameMap_b,map_mul,backward_C,backward_T_neg_one,back_b ρ Q f hf]
  · change backward ρ Q f hf (frameMap ρ Q Determinant.c)=bc Determinant.c
    rw [frameMap_c,map_mul,backward_C,backward_T_neg_one,back_c ρ Q f hf]
  · change backward ρ Q f hf (frameMap ρ Q Determinant.u)=bc Determinant.u
    rw [frameMap_u,backward_C]
    simpa only [Degeneration.coefficientMap_u,Bundle.inclusion_u] using compatibility ρ f hf Quadric.u
lemma backward_forward_j (r : Determinant.T) : backward ρ Q f hf (forward ρ Q (Bundle.j r))=ib (Bundle.j r) := by
  rw [forward_j]
  exact DFunLike.congr_fun (backward_frameMap ρ Q f hf) r
lemma backward_forward_τ : backward ρ Q f hf (forward ρ Q Bundle.τ)=ib Bundle.τ := by
  rw [forward_τ]
  change backward ρ Q f hf (C (ρ Degeneration.p))=_
  rw [backward_C,← AlgHom.comp_apply,hf]
  change ib (Bundle.pullback (Degeneration.π (MvPolynomial.X 0)))=_
  rw [Bundle.pullback_π]
  congr 1
  exact MvPolynomial.aeval_X _ 0
lemma backward_forward_V : backward ρ Q f hf (forward ρ Q Bundle.V)=ib Bundle.V := by
  have hp : ib Bundle.τ ≠ 0 := by
    have hi : Function.Injective ib := IsFractionRing.injective Bundle.B KB
    simpa only [map_zero] using hi.ne Bundle.τ_ne_zero
  apply mul_left_cancel₀ (pow_ne_zero 2 hp)
  have he := congrArg (fun z => backward ρ Q f hf (forward ρ Q z)) Bundle.equation
  rw [map_mul,map_pow,map_mul,map_pow,backward_forward_τ,backward_forward_j] at he
  rw [he,← Bundle.equation,map_mul,map_pow]
lemma backward_forward : (backward ρ Q f hf).comp (forward ρ Q)=ib := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext'
  · ext r
    exact backward_forward_j ρ Q f hf r
  · intro i
    fin_cases i
    · exact backward_forward_τ ρ Q f hf
    · exact backward_forward_V ρ Q f hf
lemma forward_injective : Function.Injective (forward ρ Q) := by
  apply Function.Injective.of_comp (f := backward ρ Q f hf)
  rw [← AlgHom.coe_comp,backward_forward]
  exact IsFractionRing.injective Bundle.B KB
end ComplexCancellation.Torsor

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.TorsorClearing ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [IsDomain P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ) (D : Derivation ℂ Degeneration.G Degeneration.G)
variable (hρ : Function.Injective ρ)
variable (hc : ∀ p, p ∈ InvariantClearing.subalgebra ρ D)
include hρ hc
lemma clear_C (p : P) : C p ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  obtain ⟨c,r,hc,hcn,hcr⟩ := hc p
  refine ⟨c,Bundle.pullback r,hc,hcn,?_⟩
  have h := DFunLike.congr_fun (forward_pullback ρ Q hρ) c
  have h' := DFunLike.congr_fun (forward_pullback ρ Q hρ) r
  change forward ρ Q (Bundle.pullback c)=C (ρ c) at h
  change forward ρ Q (Bundle.pullback r)=C (ρ r) at h'
  rw [h,h',← map_mul,hcr]
lemma clear_T_one : T 1 ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  have he : T 1=C Q.c₀*forward ρ Q (Bundle.j Determinant.a)-C Q.b₀*forward ρ Q (Bundle.j Determinant.d) := by
    rw [forward_j,forward_j,frameMap_a,frameMap_d]
    calc _ = C (Q.a₀*Q.c₀-Q.d₀*Q.b₀)*T 1 := by rw [Q.det,map_one,one_mul]
      _ = _ := by rw [map_sub,map_mul,map_mul]; ring
  rw [he]
  apply sub_mem
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
lemma clear_T_neg_one : T (-1) ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  have he : T (-1)=C Q.a₀*forward ρ Q (Bundle.j Determinant.c)-C Q.d₀*forward ρ Q (Bundle.j Determinant.b) := by
    rw [forward_j,forward_j,frameMap_c,frameMap_b]
    calc _ = C (Q.a₀*Q.c₀-Q.d₀*Q.b₀)*T (-1) := by rw [Q.det,map_one,one_mul]
      _ = _ := by rw [map_sub,map_mul,map_mul]; ring
  rw [he]
  apply sub_mem
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
lemma clear_T (n : ℤ) : T n ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  by_cases hn : 0 ≤ n
  · have he : T n=(T 1 : L (P := P))^n.toNat := by rw [T_pow,Int.toNat_of_nonneg hn,mul_one]
    rw [he]
    exact pow_mem (clear_T_one ρ Q D hρ hc) _
  · have he : T n=(T (-1) : L (P := P))^(-n).toNat := by rw [T_pow,Int.toNat_of_nonneg (by omega : 0 ≤ -n)]; congr 1; omega
    rw [he]
    exact pow_mem (clear_T_neg_one ρ Q D hρ hc) _
lemma clear_laurent (r : L (P := P)) : r ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => exact add_mem hr hs
  | C_mul_T n p => exact mul_mem (clear_C ρ Q D hρ hc p) (clear_T ρ Q D hρ hc n)
end ComplexCancellation.Torsor

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.ReplicaLift ----
namespace OAI

noncomputable section

namespace ComplexCancellation.SliceDerivative
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
lemma locallyNilpotent : LND.LocallyNilpotent (derivation (k := k) (F := F)) := by
  intro p
  exact ⟨p.natDegree+1,Polynomial.iterate_derivative_eq_zero (by omega)⟩
end ComplexCancellation.SliceDerivative

namespace ComplexCancellation.Bundle
end ComplexCancellation.Bundle

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [IsDomain P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ) (D : Derivation ℂ Degeneration.G Degeneration.G)
variable (hρ : Function.Injective ρ) (hc : ∀ p, p ∈ InvariantClearing.subalgebra ρ D)
variable (Dp : Derivation ℂ P P) (hDp : LND.LocallyNilpotent Dp) (hder : ∀ r, Dp (ρ r)=ρ (D r))
include hder in
omit [IsDomain P] in
lemma extension_base (r : Degeneration.G) : LaurentDerivation.extension Dp (base ρ r)=base ρ (D r) := by
  change LaurentDerivation.extension Dp (C (ρ r))=C (ρ (D r))
  rw [LaurentDerivation.extension_C,hder]
include hρ hc hDp hder
lemma invariant_replica (hf : Function.Injective (forward ρ Q)) :
    ∃ c : Degeneration.G, ∃ E : Derivation ℂ Bundle.B Bundle.B,
      D c=0 ∧ c≠0 ∧ LND.LocallyNilpotent E ∧
      ∀ b, forward ρ Q (E b)=base ρ c*LaurentDerivation.extension Dp (forward ρ Q b) := by
  have hbase (r : Degeneration.G) : forward ρ Q (Bundle.pullback r)=base ρ r :=
    DFunLike.congr_fun (forward_pullback ρ Q hρ) r
  obtain ⟨c,E,hDc,hcn,hE,hs⟩ := InvariantRestriction.exists_restriction Bundle.pullback (forward ρ Q) hf D
    (LaurentDerivation.extension Dp) (LaurentDerivation.locallyNilpotent Dp hDp)
    (fun r => by rw [hbase,hbase,extension_base ρ D Dp hder]) (clear_laurent ρ Q D hρ hc)
  exact ⟨c,E,hDc,hcn,hE,fun b => by rw [hs,hbase]⟩
end ComplexCancellation.Torsor

namespace ComplexCancellation.PolynomialTorsor
open PolynomialModel
variable (D : Derivation ℂ Degeneration.G Degeneration.G) (hD : LND.LocallyNilpotent D)
variable {t : K} (ht : FractionDerivation.extend D t=1)
lemma ρ_injective : Function.Injective (ρ D hD ht) := model_injective D hD ht
lemma exists_frame : Nonempty (Torsor.Frame (ρ D hD ht)) := by
  have h := congrArg (ρ D hD ht) Degeneration.equation
  simp only [map_mul,map_add,map_one] at h
  obtain ⟨a,d,b,c,hab,hdc,hdb,hdet⟩ := BezoutFrame.exists_frame _ _ _ h
  exact ⟨⟨a,d,b,c,hab,hdc,hdb,hdet⟩⟩
lemma inverseCoefficient_comp : (inverseCoefficient (D := D) (t := t)).comp (ρ D hD ht)=Torsor.ib.comp Bundle.pullback := by
  ext r
  change toField (PolynomialModel.evaluation (D := D) (t := t) (model D hD ht r))=_
  rw [evaluation_model]
  exact IsFractionRing.lift_algebraMap
    (g := (Torsor.ib.comp Bundle.pullback).toRingHom)
    ((IsFractionRing.injective Bundle.B Torsor.KB).comp Bundle.pullback_injective) r
lemma forward_injective (Q : Torsor.Frame (ρ D hD ht)) : Function.Injective (Torsor.forward (ρ D hD ht) Q) :=
  Torsor.forward_injective _ Q (inverseCoefficient (D := D) (t := t)) (inverseCoefficient_comp D hD ht)
end ComplexCancellation.PolynomialTorsor

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.LaurentEuler ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LaurentEuler
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
end ComplexCancellation.LaurentEuler

namespace ComplexCancellation.LaurentEuler
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
lemma commute_extension (D : Derivation k R R) (r : LaurentPolynomial R) :
    derivation (k := k) (LaurentDerivation.extension D r)=LaurentDerivation.extension D (derivation (k := k) r) := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => simp only [map_add,hr,hs]
  | C_mul_T n a => rw [LaurentDerivation.extension_monomial (k := k),monomial (k := k),monomial (k := k),map_zsmul,LaurentDerivation.extension_monomial (k := k)]
lemma commute_replica (D : Derivation k R R) (c : R) (r : LaurentPolynomial R) :
    derivation (k := k) (C c*LaurentDerivation.extension D r)=C c*LaurentDerivation.extension D (derivation (k := k) r) := by
  rw [Derivation.leibniz,coefficient,smul_zero,add_zero,smul_eq_mul,commute_extension]
end ComplexCancellation.LaurentEuler

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.TorsorEuler ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ)
lemma forwardEuler_τ : LaurentEuler.derivation (k := ℂ) (forward ρ Q Bundle.τ)=0 := by
  rw [forward_τ]
  exact LaurentEuler.coefficient _
lemma forwardEuler_j (r : Determinant.T) :
    LaurentEuler.derivation (k := ℂ) (forward ρ Q (Bundle.j r))=forward ρ Q (Bundle.fiberEuler (Bundle.j r)) := by
  change _=forward ρ Q (AffineModification.euler _ _ _ (AffineModification.coefficientHom (k := ℂ) _ r))
  rw [AffineModification.euler_coefficient,forward_j,frameMap_intertwining]
  exact (forward_j ρ Q (Determinant.Euler r)).symm
variable [IsDomain P]
lemma forwardEuler_V (hρ : Function.Injective ρ) :
    LaurentEuler.derivation (k := ℂ) (forward ρ Q Bundle.V)=2*forward ρ Q Bundle.V := by
  have hτ : forward ρ Q Bundle.τ≠0 := by rw [forward_τ]; exact base_p_ne_zero ρ hρ
  apply mul_left_cancel₀ (pow_ne_zero 2 hτ)
  have he := congrArg (LaurentEuler.derivation (k := ℂ) : L (P := P) → L (P := P))
    (congrArg (forward ρ Q) Bundle.equation)
  rw [map_mul,map_pow,Derivation.leibniz,Derivation.leibniz_pow,forwardEuler_τ,
    smul_zero,smul_zero,smul_zero,add_zero,smul_eq_mul,forward_j,frameMap_intertwining,
    Determinant.Euler_v,map_mul,map_ofNat] at he
  rw [he,← forward_j,← Bundle.equation,map_mul,map_pow]
  ring
lemma forward_intertwining (hρ : Function.Injective ρ) (r : Bundle.B) :
    LaurentEuler.derivation (k := ℂ) (forward ρ Q r)=forward ρ Q (Bundle.fiberEuler r) := by
  change r ∈ DerivationIntertwining.subalgebra (forward ρ Q) Bundle.fiberEuler LaurentEuler.derivation
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective Determinant.T (Ideal.span {AffineModification.rel Determinant.T Determinant.v}) r
  change AffineModification.π Determinant.T Determinant.v p ∈ _
  induction p using MvPolynomial.induction_on with
  | C a => exact forwardEuler_j ρ Q a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    apply mul_mem hp
    fin_cases i
    · change LaurentEuler.derivation (k := ℂ) (forward ρ Q Bundle.τ)=forward ρ Q (Bundle.fiberEuler Bundle.τ)
      rw [forwardEuler_τ]
      change 0=forward ρ Q (AffineModification.euler _ _ _ (AffineModification.τ _ _))
      rw [AffineModification.euler_τ,map_zero]
    · change LaurentEuler.derivation (k := ℂ) (forward ρ Q Bundle.V)=forward ρ Q (Bundle.fiberEuler Bundle.V)
      rw [forwardEuler_V ρ Q hρ]
      change _=forward ρ Q (AffineModification.euler _ _ _ (AffineModification.V _ _))
      rw [AffineModification.euler_V,map_mul,map_ofNat]
      rfl
lemma replica_commute (hρ : Function.Injective ρ) (hf : Function.Injective (forward ρ Q))
    (Dp : Derivation ℂ P P) (E : Derivation ℂ Bundle.B Bundle.B) (c : Degeneration.G)
    (hs : ∀ b, forward ρ Q (E b)=base ρ c*LaurentDerivation.extension Dp (forward ρ Q b))
    (b : Bundle.B) : Bundle.fiberEuler (E b)=E (Bundle.fiberEuler b) := by
  apply hf
  rw [← forward_intertwining ρ Q hρ,hs,hs,← forward_intertwining ρ Q hρ]
  exact LaurentEuler.commute_replica Dp (ρ c) (forward ρ Q b)
end ComplexCancellation.Torsor

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.EquivariantLift ----
namespace OAI

noncomputable section

namespace ComplexCancellation.PolynomialTorsor
open PolynomialModel
lemma exists_equivariant_lift (D : Derivation ℂ Degeneration.G Degeneration.G)
    (hD : LND.LocallyNilpotent D) (hDn : D ≠ 0) :
    ∃ (c : Degeneration.G) (E : Derivation ℂ Bundle.B Bundle.B),
      c ≠ 0 ∧ LND.LocallyNilpotent E ∧ E ≠ 0 ∧
      (∀ r, E (Bundle.pullback r)=Bundle.pullback (c*D r)) ∧
      ∀ b, Bundle.fiberEuler (E b)=E (Bundle.fiberEuler b) := by
  obtain ⟨s,hs,hss⟩ := local_slice D hD hDn
  let t : K := ι (k := ℂ) s/ι (k := ℂ) (D s)
  have hi : Function.Injective (ι (k := ℂ) (R := Degeneration.G)) :=
    IsFractionRing.injective Degeneration.G K
  have hsn : ι (k := ℂ) (D s) ≠ 0 := by simpa only [map_zero] using hi.ne hs
  have ht : FractionDerivation.extend D t=1 := by
    change FractionDerivation.extend D (algebraMap Degeneration.G K s/algebraMap Degeneration.G K (D s))=1
    rw [Derivation.leibniz_div_const _ _ _ (by rw [FractionDerivation.extend_algebraMap,hss,map_zero]),
      FractionDerivation.extend_algebraMap,smul_eq_mul]
    exact inv_mul_cancel₀ hsn
  let φ := ρ D hD ht
  have hφ : Function.Injective φ := ρ_injective D hD ht
  obtain ⟨Q⟩ := exists_frame D hD ht
  have hf : Function.Injective (Torsor.forward φ Q) := forward_injective D hD ht Q
  let Dp : Derivation ℂ (P D) (P D) := SliceDerivative.derivation
  have hDp : LND.LocallyNilpotent Dp := SliceDerivative.locallyNilpotent
  have hder (r : Degeneration.G) : Dp (φ r)=φ (D r) := derivative_model D hD ht r
  have hc (p : P D) : p ∈ InvariantClearing.subalgebra φ D :=
    clear_polynomial D hD ht s hs hss rfl p
  obtain ⟨c,E,hDc,hcn,hE,hsE⟩ := Torsor.invariant_replica φ Q D hφ hc Dp hDp hder hf
  have hbase (r : Degeneration.G) : Torsor.forward φ Q (Bundle.pullback r)=Torsor.base φ r :=
    DFunLike.congr_fun (Torsor.forward_pullback φ Q hφ) r
  have he (r : Degeneration.G) : E (Bundle.pullback r)=Bundle.pullback (c*D r) := by
    apply hf
    rw [hsE,hbase,Torsor.extension_base φ D Dp hder,hbase,map_mul]
  have hEn : E ≠ 0 := by
    intro hz
    apply hDn
    ext r
    have h := he r
    rw [hz,Derivation.zero_apply] at h
    have hz' : c*D r=0 := Bundle.pullback_injective (by simpa only [map_zero] using h.symm)
    exact (mul_eq_zero.mp hz').resolve_left hcn
  exact ⟨c,E,hcn,hE,hEn,he,Torsor.replica_commute φ Q hφ hf Dp E c hsE⟩
end ComplexCancellation.PolynomialTorsor

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.PolynomialTorsor
open PolynomialModel


theorem solution : type_of% @_root_.OAI.ComplexCancellation.PolynomialTorsor.exists_equivariant_lift := @_root_.OAI.ComplexCancellation.PolynomialTorsor.exists_equivariant_lift
