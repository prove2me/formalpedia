-- Prove2me | solution 1 for M4aHerbrand.valuation_adelicNorm_eq_finprod_pow_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/83764871-6235-586d-ad6b-217efd6ed2f7

import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_adeleBaseChange_local_rigidity
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_valuation_adelicNorm_eq_finprod_pow_inertiaDeg
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain M4aHerbrand
open scoped TensorProduct

noncomputable section

namespace M4aHerbrandA2Sol

open Module

theorem norm_transport {ι R S R' S' : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] [Algebra R S] [CommRing R'] [CommRing S'] [Algebra R' S']
    (bS : Module.Basis ι R S) (c : Module.Basis ι R' S') (π : R →+* R') (P : S →+* S')
    (hP : ∀ (r : R) (s : S), P (r • s) = π r • P s) (hb : ∀ i, P (bS i) = c i) (x : S) :
    π (Algebra.norm R x) = Algebra.norm R' (P x) := by
  rw [Algebra.norm_eq_matrix_det bS, Algebra.norm_eq_matrix_det c, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]
  have hx : P x * c j = ∑ k, π (bS.repr (x * bS j) k) • c k := by
    rw [← hb j, ← map_mul]
    conv_lhs => rw [← bS.sum_repr (x * bS j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP, hb]
  rw [hx, c.repr_sum_self]

universe u v

section DetPi

variable {R : Type*} [CommRing R] {ι : Type*}
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

def piMap (f : ∀ i, M i →ₗ[R] M i) : (∀ i, M i) →ₗ[R] (∀ i, M i) :=
  LinearMap.pi fun i => (f i).comp (LinearMap.proj i)

@[scoped simp] theorem piMap_apply (f : ∀ i, M i →ₗ[R] M i) (x : ∀ i, M i) (i : ι) :
    piMap f x i = f i (x i) :=
  rfl

end DetPi

section DetPiInduction

variable {R : Type*} [CommRing R]

theorem det_pi' (ι₀ : Type u) [Fintype ι₀] :
    ∀ {M : ι₀ → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
      (f : ∀ i, M i →ₗ[R] M i), (piMap f).det = ∏ i, (f i).det := by
  refine Fintype.induction_empty_option
    (P := fun γ instγ =>
      ∀ {M : γ → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
        [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
        (f : ∀ i, M i →ₗ[R] M i),
        (piMap f).det = (@Finset.univ γ instγ).prod fun i => (f i).det)
    ?of_equiv ?h_empty ?h_option ι₀
  case of_equiv =>
    intro α β _ e ih M _ _ _ _ f
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let E := LinearEquiv.piCongrLeft R M e
    have hE : ∀ (y : ∀ a, M (e a)) (a), E y (e a) = y a := fun y a =>
      show Equiv.piCongrLeft M e y (e a) = y a from Equiv.piCongrLeft_apply_apply M e y a
    have hEs : ∀ (x : ∀ b, M b) (a), E.symm x a = x (e a) := fun x a =>
      show Equiv.piCongrLeft' M e.symm x a = x (e a) from rfl
    have hconj : piMap f
        = (E : (∀ a, M (e a)) →ₗ[R] ∀ b, M b) ∘ₗ (piMap fun a => f (e a))
            ∘ₗ (E.symm : (∀ b, M b) →ₗ[R] ∀ a, M (e a)) := by
      apply LinearMap.ext
      intro x
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      show f (e a) (x (e a)) = E ((piMap fun a => f (e a)) (E.symm x)) (e a)
      rw [hE]
      show f (e a) (x (e a)) = f (e a) (E.symm x a)
      rw [hEs]
    rw [hconj, LinearMap.det_conj, ih]
    exact Fintype.prod_equiv e (fun a => (f (e a)).det) (fun b => (f b).det) fun a => rfl
  case h_empty =>
    intro M _ _ _ _ f
    haveI : Subsingleton (∀ i : PEmpty, M i) := ⟨fun a b => funext fun i => i.elim⟩
    rw [LinearMap.det_eq_one_of_subsingleton, Finset.prod_of_isEmpty]
  case h_option =>
    intro α _ ih M _ _ _ _ f
    let E : (M none × ∀ a, M (some a)) ≃ₗ[R] ∀ i, M i :=
      (LinearEquiv.piOptionEquivProd R).symm
    have hconj : piMap f
        = (E : _ →ₗ[R] ∀ i, M i) ∘ₗ ((f none).prodMap (piMap fun a => f (some a)))
            ∘ₗ (E.symm : (∀ i, M i) →ₗ[R] _) := by
      apply LinearMap.ext
      intro x
      funext i
      cases i <;> rfl
    rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, ih, Fintype.prod_option]

end DetPiInduction

section NormPi

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
variable {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]

omit [Fintype ι] in
theorem lmul_pi (x : ∀ i, S i) :
    Algebra.lmul R (∀ i, S i) x = piMap fun i => Algebra.lmul R (S i) (x i) := by
  apply LinearMap.ext
  intro y
  rfl

theorem norm_pi [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (x : ∀ i, S i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  rw [Algebra.norm_apply, show Algebra.lmul R (∀ i, S i) x
      = piMap fun i => Algebra.lmul R (S i) (x i) from lmul_pi x, det_pi']
  rfl

end NormPi

section A

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def evalAt (w : HeightOneSpectrum (𝓞 L)) : FiniteAdeleRing (𝓞 L) L →+* w.adicCompletion L where
  toFun x := x w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def projPi (v : HeightOneSpectrum (𝓞 K)) :
    AdeleRing (𝓞 L) L →+* (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  RingHom.pi fun w => (evalAt L w.1).comp (RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem projPi_apply (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    projPi K L v x w = (x.2 : FiniteAdeleRing (𝓞 L) L) w.1 := rfl

def adeleBasis (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    letI := B.β.toAlgebra
    Module.Basis (Fin (Module.finrank K L)) (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  letI := B.β.toAlgebra
  (Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) (Module.finBasis K L)).map B.tensorEquiv.toLinearEquiv

theorem adeleBasis_apply (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (i : Fin (Module.finrank K L)) :
    (letI := B.β.toAlgebra; adeleBasis K L B i) = algebraMap L (AdeleRing (𝓞 L) L) (Module.finBasis K L i) := by
  letI := B.β.toAlgebra
  show ((Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) (Module.finBasis K L)).map
    B.tensorEquiv.toLinearEquiv) i = _
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.basis_apply]
  exact B.tensorEquiv_one_tmul _

open scoped TensorProduct.RightActions in

def piBasis (v : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (Fin (Module.finrank K L)) (v.adicCompletion K) (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  ((Module.finBasis K L).rightBaseChange L).map
    (LinearEquiv.ofBijective (HeightOneSpectrum.adicCompletion.baseChangeRight K L (𝓞 L) v).toLinearMap
      (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v))

open scoped TensorProduct.RightActions in
theorem piBasis_apply (v : HeightOneSpectrum (𝓞 K)) (i : Fin (Module.finrank K L)) :
    piBasis K L v i =
      algebraMap L (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) (Module.finBasis K L i) := by
  show (((Module.finBasis K L).rightBaseChange L).map _) i = _
  rw [Module.Basis.map_apply, Module.Basis.rightBaseChange_apply, LinearEquiv.ofBijective_apply]
  exact SemialgHom.baseChange_of_algebraMap_tmul_left
    (HeightOneSpectrum.adicCompletion.semialgHomPi K L (𝓞 L) v) _

theorem projPi_algebraMap (v : HeightOneSpectrum (𝓞 K)) (l : L) :
    projPi K L v (algebraMap L (AdeleRing (𝓞 L) L) l) =
      algebraMap L (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) l := by
  funext w
  rw [projPi_apply, Pi.algebraMap_apply]
  exact NumberField.AdeleRing.algebraMap_snd_apply (𝓞 L) L l w.1

theorem projPi_smul (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (v : HeightOneSpectrum (𝓞 K))
    (r : AdeleRing (𝓞 K) K) (s : AdeleRing (𝓞 L) L) :
    projPi K L v (B.β r * s) =
      algebraMap (v.adicCompletion K) (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L)
        ((r.2 : FiniteAdeleRing (𝓞 K) K) v) * projPi K L v s := by
  rw [map_mul]
  congr 1
  funext w
  rw [projPi_apply, Pi.algebraMap_apply, (M4aHerbrand.adeleBaseChange_local_rigidity K L B).1 r w.1]

  obtain ⟨w, hw⟩ := w
  subst hw
  rfl

theorem a2_impl (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (x : AdeleRing (𝓞 L) L) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((B.adelicNorm x).2 : FiniteAdeleRing (𝓞 K) K) v) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 L),
        Valued.v ((x.2 : FiniteAdeleRing (𝓞 L) L) w) ^ Ideal.inertiaDeg' v.asIdeal w.asIdeal := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := B.β.toAlgebra

  have h1 : ((B.adelicNorm x).2 : FiniteAdeleRing (𝓞 K) K) v =
      Algebra.norm (v.adicCompletion K) (projPi K L v x) := by
    have key := norm_transport (adeleBasis K L B) (piBasis K L v)
      ((evalAt K v).comp (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) (projPi K L v)
      (fun r s => by
        rw [Algebra.smul_def, Algebra.smul_def]
        exact projPi_smul K L B v r s)
      (fun i => by rw [adeleBasis_apply, piBasis_apply, projPi_algebraMap]) x
    exact key

  letI hft : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v

  letI : Fintype {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} := hft
  haveI : ∀ w : v.Extension (𝓞 L), Module.Free (v.adicCompletion K) (w.1.adicCompletion L) :=
    fun w => Module.Free.of_divisionRing _ _
  rw [h1, norm_pi, map_prod]
  simp_rw [M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg, projPi_apply]

  symm
  rw [finprod_eq_prod_of_mulSupport_subset _
    (s := (Finset.univ : Finset (v.Extension (𝓞 L))).map (Function.Embedding.subtype _)) ?_,
    Finset.prod_map]
  · rfl
  · intro w hw
    by_cases h : w.under (𝓞 K) = v
    · rw [Finset.mem_coe, Finset.mem_map]
      exact ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩
    · exfalso
      apply hw
      have h0 : Ideal.inertiaDeg' v.asIdeal w.asIdeal = 0 := by
        unfold Ideal.inertiaDeg'
        rw [dif_neg]
        intro hc
        apply h
        ext1
        rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def]
        exact hc
      simp only [h0, pow_zero]

end A

end M4aHerbrandA2Sol
p2m_reactivate "P2MW.S_M4aHerbrand_valuation_adelicNorm_eq_finprod_pow_inertiaDeg.M4aHerbrandA2Sol"

end
p2m_reactivate "P2MW.S_M4aHerbrand_valuation_adelicNorm_eq_finprod_pow_inertiaDeg.M4aHerbrandA2Sol"

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (x : AdeleRing (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((B.adelicNorm x).2 : FiniteAdeleRing (𝓞 K) K) v) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 L),
        Valued.v ((x.2 : FiniteAdeleRing (𝓞 L) L) w) ^ Ideal.inertiaDeg' v.asIdeal w.asIdeal :=
  M4aHerbrandA2Sol.a2_impl K L B x v

#print axioms solution

end S_M4aHerbrand_valuation_adelicNorm_eq_finprod_pow_inertiaDeg
end P2MW
export P2MW.S_M4aHerbrand_valuation_adelicNorm_eq_finprod_pow_inertiaDeg (solution)
