-- Prove2me | solution 1 for M4aHerbrand.AdeleBaseChange.mem_range_idelicNorm_of_forall_exists_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/559d4e6a-c3f7-5195-8b52-12f9abe432d4

import Mathlib
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_adeleBaseChange_local_rigidity
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

section PartN

set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand
open scoped TensorProduct

noncomputable section

namespace P2mS26N0

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

theorem adelicNorm_snd_apply (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (x : AdeleRing (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 K)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    ((B.adelicNorm x).2 : FiniteAdeleRing (𝓞 K) K) v =
      ∏ w : v.Extension (𝓞 L), Algebra.norm (v.adicCompletion K) ((x.2 : FiniteAdeleRing (𝓞 L) L) w.1) := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := B.β.toAlgebra
  letI hft : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have h1 : ((B.adelicNorm x).2 : FiniteAdeleRing (𝓞 K) K) v =
      Algebra.norm (v.adicCompletion K) (projPi K L v x) :=
    norm_transport (adeleBasis K L B) (piBasis K L v)
      ((evalAt K v).comp (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) (projPi K L v)
      (fun r s => by
        rw [Algebra.smul_def, Algebra.smul_def]
        exact projPi_smul K L B v r s)
      (fun i => by rw [adeleBasis_apply, piBasis_apply, projPi_algebraMap]) x
  haveI : ∀ w : v.Extension (𝓞 L), Module.Free (v.adicCompletion K) (w.1.adicCompletion L) :=
    fun w => Module.Free.of_divisionRing _ _
  rw [h1, norm_pi]
  rfl

section Arch

open NumberField.InfinitePlace M4aHerbrand.ArchSemilocal
open scoped NumberField.LiesOver

attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver

def projInf (v : InfinitePlace K) : AdeleRing (𝓞 L) L →+* (∀ w : v.Extension L, w.1.Completion) :=
  RingHom.pi fun w => (Pi.evalRingHom (fun w' : InfinitePlace L => w'.Completion) w.1).comp
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

omit [NumberField K] in
theorem projInf_apply (v : InfinitePlace K) (x : AdeleRing (𝓞 L) L) (w : v.Extension L) :
    projInf K L v x w = (x.1 : InfiniteAdeleRing L) w.1 := rfl

def piBasisInf (v : InfinitePlace K) :
    Module.Basis (Fin (Module.finrank K L)) v.Completion (∀ w : v.Extension L, w.1.Completion) :=
  (Algebra.TensorProduct.basis v.Completion (Module.finBasis K L)).map
    (placeEquivAlg (K := K) (L := L) v).toLinearEquiv

theorem piBasisInf_apply (v : InfinitePlace K) (i : Fin (Module.finrank K L)) :
    piBasisInf K L v i = algebraMap L (∀ w : v.Extension L, w.1.Completion) (Module.finBasis K L i) := by
  show ((Algebra.TensorProduct.basis v.Completion (Module.finBasis K L)).map
    (placeEquivAlg (K := K) (L := L) v).toLinearEquiv) i = _
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.basis_apply]
  funext w
  show psi (K := K) (L := L) v ((1 : v.Completion) ⊗ₜ[K] Module.finBasis K L i) w = _
  rw [psi_apply, psiFactor_one_tmul]
  rfl

omit [NumberField K] in
theorem projInf_algebraMap (v : InfinitePlace K) (l : L) :
    projInf K L v (algebraMap L (AdeleRing (𝓞 L) L) l) =
      algebraMap L (∀ w : v.Extension L, w.1.Completion) l := by
  funext w
  rw [projInf_apply, Pi.algebraMap_apply]
  exact NumberField.AdeleRing.algebraMap_fst_apply (𝓞 L) L l w.1

theorem conorm_apply_ext (x : InfiniteAdeleRing K) (v : InfinitePlace K) (w : v.Extension L) :
    (genuineInfinitePlaceData (K := K) (L := L)).conorm x w.1 = algebraMap v.Completion w.1.Completion (x v) := by
  obtain ⟨w, rfl⟩ := w
  haveI : w.1.LiesOver (w.comap (algebraMap K L)).1 := liesOver_of_comap_eq rfl
  show psiFactor (w.comap (algebraMap K L)) w ((x (w.comap (algebraMap K L))) ⊗ₜ[K] (1 : L)) = _
  rw [psiFactor_tmul, map_one, mul_one]

theorem projInf_smul (v : InfinitePlace K) (r : AdeleRing (𝓞 K) K) (s : AdeleRing (𝓞 L) L) :
    projInf K L v ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).β r * s) =
      algebraMap v.Completion (∀ w : v.Extension L, w.1.Completion) ((r.1 : InfiniteAdeleRing K) v)
        * projInf K L v s := by
  rw [map_mul]
  congr 1
  funext w
  rw [projInf_apply, Pi.algebraMap_apply, M4aHerbrand.GenuineDescent.genuineBaseChange_β,
    M4aHerbrand.Bridge.genuineβ_fst]
  exact conorm_apply_ext K L r.1 v w

open scoped Classical in

theorem adelicNorm_fst_apply (x : AdeleRing (𝓞 L) L) (v : InfinitePlace K) :
    (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).adelicNorm x).1 : InfiniteAdeleRing K) v =
      ∏ w : v.Extension L, Algebra.norm v.Completion ((x.1 : InfiniteAdeleRing L) w.1) := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toAlgebra
  have h1 : (((M4aHerbrand.GenuineDescent.genuineBaseChange K L).adelicNorm x).1 : InfiniteAdeleRing K) v =
      Algebra.norm v.Completion (projInf K L v x) :=
    norm_transport (adeleBasis K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L)) (piBasisInf K L v)
      ((Pi.evalRingHom (fun v' : InfinitePlace K => v'.Completion) v).comp
        (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) (projInf K L v)
      (fun r s => by
        rw [Algebra.smul_def, Algebra.smul_def]
        exact projInf_smul K L v r s)
      (fun i => by rw [adeleBasis_apply, piBasisInf_apply, projInf_algebraMap]) x
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  haveI : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing _ _
  rw [h1, norm_pi]
  rfl

omit [NumberField K] [NumberField L] in

theorem finrank_completion_eq (v : InfinitePlace K) (w : v.Extension L) :
    Module.finrank v.Completion w.1.Completion = 1 ∨
      (Module.finrank v.Completion w.1.Completion = 2 ∧ v.IsReal ∧ ¬ w.1.IsUnramified K) := by
  by_cases h : w.1.IsUnramified K
  · exact Or.inl (Completion.finrank_eq_one_of_isUnramified v h)
  · refine Or.inr ⟨Completion.finrank_eq_two_of_isRamified v h, ?_, h⟩
    have hr := (InfinitePlace.isRamified_iff.mp h).2
    rwa [w.2] at hr

omit [NumberField K] [NumberField L] in

theorem exists_sq_eq_of_pos (v : InfinitePlace K) (hv : v.IsReal) (t : v.Completion)
    (ht : 0 < Completion.extensionEmbeddingOfIsReal hv t) : ∃ c : v.Completion, c ^ 2 = t := by
  obtain ⟨c, hc⟩ := Completion.surjective_extensionEmbeddingOfIsReal hv
    (Real.sqrt (Completion.extensionEmbeddingOfIsReal hv t))
  refine ⟨c, (Completion.bijective_extensionEmbeddingOfIsReal hv).1 ?_⟩
  rw [map_pow, hc, Real.sq_sqrt ht.le]

set_option synthInstance.maxHeartbeats 1600000 in
omit [NumberField K] in
open scoped Classical in

theorem exists_arch_local [IsGalois K L] (v : InfinitePlace K) (t : v.Completion) (ht0 : t ≠ 0)
    (hpos : ∀ hv : v.IsReal, ¬ v.IsUnramifiedIn L → 0 < Completion.extensionEmbeddingOfIsReal hv t) :
    ∃ z : ∀ w : v.Extension L, w.1.Completion,
      (∀ w, z w ≠ 0) ∧ ∏ w : v.Extension L, Algebra.norm v.Completion (z w) = t := by
  obtain ⟨w₀', hw₀'⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  obtain ⟨w₀⟩ : Nonempty (v.Extension L) := ⟨⟨w₀', hw₀'⟩⟩
  haveI : FiniteDimensional v.Completion w₀.1.Completion := finiteDimensional_completion v w₀.1

  obtain ⟨c, hc⟩ : ∃ c : v.Completion, c ^ Module.finrank v.Completion w₀.1.Completion = t := by
    rcases finrank_completion_eq K L v w₀ with h1 | ⟨h2, hv, hram⟩
    · exact ⟨t, by rw [h1, pow_one]⟩
    · have hIn : ¬ v.IsUnramifiedIn L := by
        rw [← w₀.2, InfinitePlace.isUnramifiedIn_comap]
        exact hram
      obtain ⟨c, hc⟩ := exists_sq_eq_of_pos K v hv t (hpos hv hIn)
      exact ⟨c, by rw [h2, hc]⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow Module.finrank_pos.ne'] at hc
    exact ht0 hc.symm
  refine ⟨Pi.mulSingle w₀ (algebraMap v.Completion w₀.1.Completion c), fun w => ?_, ?_⟩
  · by_cases hw : w = w₀
    · subst hw
      rw [Pi.mulSingle_eq_same]
      exact (map_ne_zero _).mpr hc0
    · rw [Pi.mulSingle_eq_of_ne hw]
      exact one_ne_zero
  · rw [Finset.prod_eq_single w₀ (fun w _ hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one])
      (fun h => absurd (Finset.mem_univ w₀) h), Pi.mulSingle_eq_same, Algebra.norm_algebraMap, hc]

end Arch

section R0

variable {K L}

theorem adelicNorm_eq_norm_symm (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (y : AdeleRing (𝓞 L) L) :
    letI := B.β.toAlgebra
    B.adelicNorm y = Algebra.norm (AdeleRing (𝓞 K) K) (B.tensorEquiv.symm y) := by
  letI := B.β.toAlgebra
  show Algebra.norm (AdeleRing (𝓞 K) K) y = _
  conv_lhs => rw [← B.tensorEquiv.apply_symm_apply y]
  exact Algebra.norm_eq_of_algEquiv B.tensorEquiv _

theorem idelicNorm_range_eq_std (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    B.idelicNorm.range =
      (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) :
        ((AdeleRing (𝓞 K) K) ⊗[K] L) →* AdeleRing (𝓞 K) K)).range := by
  letI := B.β.toAlgebra
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    let e : AdeleRing (𝓞 L) L ≃* ((AdeleRing (𝓞 K) K) ⊗[K] L) :=
      (B.tensorEquiv.symm : AdeleRing (𝓞 L) L ≃ₐ[AdeleRing (𝓞 K) K] _).toRingEquiv.toMulEquiv
    refine ⟨Units.mapEquiv e u, Units.ext ?_⟩
    show Algebra.norm (AdeleRing (𝓞 K) K) (B.tensorEquiv.symm (u : AdeleRing (𝓞 L) L)) =
      B.adelicNorm (u : AdeleRing (𝓞 L) L)
    exact (adelicNorm_eq_norm_symm B _).symm
  · rintro ⟨w, rfl⟩
    let e' : ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃* AdeleRing (𝓞 L) L :=
      (B.tensorEquiv : _ ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L).toRingEquiv.toMulEquiv
    refine ⟨Units.mapEquiv e' w, Units.ext ?_⟩
    show B.adelicNorm (B.tensorEquiv (w : (AdeleRing (𝓞 K) K) ⊗[K] L)) =
      Algebra.norm (AdeleRing (𝓞 K) K) (w : (AdeleRing (𝓞 K) K) ⊗[K] L)
    rw [adelicNorm_eq_norm_symm B]
    exact congrArg _ (B.tensorEquiv.symm_apply_apply _)

theorem idelicNorm_range_eq (B B' : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    B.idelicNorm.range = B'.idelicNorm.range :=
  (idelicNorm_range_eq_std B).trans (idelicNorm_range_eq_std B').symm

theorem adelicNorm_β (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (x : AdeleRing (𝓞 K) K) :
    B.adelicNorm (B.β x) = x ^ Module.finrank K L := by
  letI := B.β.toAlgebra
  rw [adelicNorm_eq_norm_symm B]
  have hx : B.tensorEquiv.symm (B.β x) = algebraMap (AdeleRing (𝓞 K) K) ((AdeleRing (𝓞 K) K) ⊗[K] L) x := by
    apply B.tensorEquiv.injective
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    rfl
  rw [hx, Algebra.norm_algebraMap_of_basis
      (Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) (Module.Free.chooseBasis K L)),
    Module.finrank_eq_card_chooseBasisIndex]

theorem idelicNorm_β (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (u : (AdeleRing (𝓞 K) K)ˣ) :
    B.idelicNorm (Units.map (B.β : AdeleRing (𝓞 K) K →* AdeleRing (𝓞 L) L) u) = u ^ Module.finrank K L :=
  Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    exact adelicNorm_β B (u : AdeleRing (𝓞 K) K))

end R0

end A

end P2mS26N0
p2m_reactivate "P2MW.S_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq.P2mS26N0"

end
p2m_reactivate "P2MW.S_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq.P2mS26N0"

end PartN
p2m_reactivate "P2MW.S_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq.P2mS26N0"

section P2mS26N0Assembly

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum M4aHerbrand M4aHerbrand.ArchSemilocal
open scoped Classical NumberField.LiesOver

attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver

namespace P2mS26N0

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem exists_arch_local' (v : InfinitePlace K) (t : v.Completion) (ht0 : t ≠ 0)
    (hpos : ∀ hv : v.IsReal, (∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → w.IsComplex) →
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv t) :
    ∃ z : ∀ w : v.Extension L, w.1.Completion,
      (∀ w, z w ≠ 0) ∧ ∏ w : v.Extension L, Algebra.norm v.Completion (z w) = t := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  obtain ⟨w₀, c, hc⟩ : ∃ (w₀ : v.Extension L) (c : v.Completion),
      c ^ Module.finrank v.Completion w₀.1.Completion = t := by
    by_cases hex : ∃ w : v.Extension L, Module.finrank v.Completion w.1.Completion = 1
    · obtain ⟨w₀, h1⟩ := hex
      exact ⟨w₀, t, by rw [h1, pow_one]⟩
    · obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
      refine ⟨⟨w', hw'⟩, ?_⟩
      rcases finrank_completion_eq K L v ⟨w', hw'⟩ with h1 | ⟨h2, hv, _⟩
      · exact absurd ⟨_, h1⟩ hex
      · have hall : ∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → w.IsComplex := by
          intro w hw
          rcases finrank_completion_eq K L v ⟨w, hw⟩ with h1' | ⟨_, _, hram⟩
          · exact absurd ⟨_, h1'⟩ hex
          · exact (InfinitePlace.isRamified_iff.mp hram).1
        obtain ⟨c, hc⟩ := exists_sq_eq_of_pos K v hv t (hpos hv hall)
        exact ⟨c, by rw [h2, hc]⟩
  haveI : FiniteDimensional v.Completion w₀.1.Completion := finiteDimensional_completion v w₀.1
  haveI : Module.Free v.Completion w₀.1.Completion := Module.Free.of_divisionRing _ _
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow Module.finrank_pos.ne'] at hc
    exact ht0 hc.symm
  refine ⟨Pi.mulSingle w₀ (algebraMap v.Completion w₀.1.Completion c), fun w => ?_, ?_⟩
  · by_cases hw : w = w₀
    · subst hw
      rw [Pi.mulSingle_eq_same]
      exact (map_ne_zero _).mpr hc0
    · rw [Pi.mulSingle_eq_of_ne hw]
      exact one_ne_zero
  · rw [Finset.prod_eq_single w₀ (fun w _ hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one])
      (fun h => absurd (Finset.mem_univ w₀) h), Pi.mulSingle_eq_same, Algebra.norm_algebraMap, hc]

theorem unit_fst_ne_zero (u : (AdeleRing (𝓞 K) K)ˣ) (v : InfinitePlace K) :
    ((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v ≠ 0 := by
  intro h
  have h1 : ((↑u⁻¹ : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v * ((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v =
      (1 : v.Completion) :=
    congrArg (fun a : AdeleRing (𝓞 K) K => (a.1 : InfiniteAdeleRing K) v) u.inv_mul
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

theorem unit_snd_ne_zero (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ≠ 0 := by
  intro h
  have h1 : ((↑u⁻¹ : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = (1 : v.adicCompletion K) :=
    congrArg (fun a : AdeleRing (𝓞 K) K => (a.2 : FiniteAdeleRing (𝓞 K) K) v) u.inv_mul
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

theorem eventually_v_snd_eq_one (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K :=
    ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K).2
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ((↑u⁻¹ : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K :=
    ((↑u⁻¹ : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K).2
  have h3 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
    filter_upwards [h1, h2] with v hv hv'
    rw [mem_adicCompletionIntegers] at hv hv'
    have hmul : ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
        ((↑u⁻¹ : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 :=
      congrArg (fun a : AdeleRing (𝓞 K) K => (a.2 : FiniteAdeleRing (𝓞 K) K) v) u.mul_inv
    have h4 := congrArg Valued.v hmul
    rw [Valuation.map_mul, Valuation.map_one] at h4
    refine le_antisymm hv ?_
    calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) *
            Valued.v (((↑u⁻¹ : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) := h4.symm
      _ ≤ Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) * 1 := by gcongr
      _ = _ := mul_one _
  exact h3

theorem v_eq_one_of_v_norm_eq_one (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (y : w.1.adicCompletion L) (h : Valued.v (Algebra.norm (v.adicCompletion K) y) = 1) :
    Valued.v y = 1 := by
  rw [M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg K L v w y] at h
  haveI : w.1.asIdeal.LiesOver v.asIdeal := ⟨by
    have h' := congrArg HeightOneSpectrum.asIdeal w.2
    rw [HeightOneSpectrum.under_asIdeal] at h'
    exact h'.symm⟩
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hf : Ideal.inertiaDeg' v.asIdeal w.1.asIdeal ≠ 0 := (Ideal.inertiaDeg'_pos v.asIdeal w.1.asIdeal).ne'
  rcases lt_trichotomy (Valued.v y) 1 with hlt | heq | hgt
  · exact absurd h (pow_lt_one₀ zero_le' hlt hf).ne
  · exact heq
  · exact absurd h (one_lt_pow₀ hgt hf).ne'

theorem mem_range_genuine (u : (AdeleRing (𝓞 K) K)ˣ)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ (w : v.Extension (𝓞 L)) (y : w.1.adicCompletion L),
      Algebra.norm (v.adicCompletion K) y = ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)
    (harch : ∀ (v : InfinitePlace K) (hv : v.IsReal),
      (∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → w.IsComplex) →
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v)) :
    u ∈ (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range := by
  choose z hz0 hzN using fun v : InfinitePlace K =>
    exists_arch_local' (K := K) (L := L) v _ (unit_fst_ne_zero u v) (fun hv hall => harch v hv hall)
  choose w₀ y hyN using hfin

  let Y : ∀ v : HeightOneSpectrum (𝓞 K), ∀ w : v.Extension (𝓞 L), w.1.adicCompletion L :=
    fun v => Pi.mulSingle (w₀ v) (y v)
  have hy0 : ∀ v, y v ≠ 0 := fun v h => by
    haveI : Module.Free (v.adicCompletion K) ((w₀ v).1.adicCompletion L) := Module.Free.of_divisionRing _ _
    have h1 := hyN v
    rw [h, Algebra.norm_zero] at h1
    exact unit_snd_ne_zero u v h1.symm
  have hY0 : ∀ v w, Y v w ≠ 0 := fun v w => by
    by_cases hw : w = w₀ v
    · subst hw
      dsimp only [Y]
      rw [Pi.mulSingle_eq_same]
      exact hy0 v
    · dsimp only [Y]
      rw [Pi.mulSingle_eq_of_ne hw]
      exact one_ne_zero
  have hYN : ∀ v, (letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
      ∏ w, Algebra.norm (v.adicCompletion K) (Y v w)) = ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := by
    intro v
    letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    dsimp only [Y]
    rw [Fintype.prod_eq_single (w₀ v) (fun w hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one]),
      Pi.mulSingle_eq_same, hyN]

  have hY1 : ∀ v, Valued.v (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 →
      ∀ w, Valued.v (Y v w) = 1 := by
    intro v hv w
    by_cases hw : w = w₀ v
    · subst hw
      dsimp only [Y]
      rw [Pi.mulSingle_eq_same]
      exact v_eq_one_of_v_norm_eq_one v (w₀ v) (y v) (by rw [hyN v, hv])
    · dsimp only [Y]
      rw [Pi.mulSingle_eq_of_ne hw, Valuation.map_one]

  let yinf : InfiniteAdeleRing L := fun w' => z (w'.comap (algebraMap K L)) ⟨w', rfl⟩
  let yfinf : ∀ w' : HeightOneSpectrum (𝓞 L), w'.adicCompletion L := fun w' => Y (w'.under (𝓞 K)) ⟨w', rfl⟩

  have hev : ∀ᶠ w' : HeightOneSpectrum (𝓞 L) in Filter.cofinite, Valued.v (yfinf w') = 1 :=
    ((M4aHerbrand.Bridge.tendsto_under_cofinite (𝓞 K) K L (𝓞 L)).eventually (eventually_v_snd_eq_one u)).mono
      fun w' hv => hY1 (w'.under (𝓞 K)) hv ⟨w', rfl⟩
  have hyfin_int : ∀ᶠ w' in Filter.cofinite, yfinf w' ∈ w'.adicCompletionIntegers L := by
    refine hev.mono fun w' hw' => ?_
    rw [mem_adicCompletionIntegers]
    exact le_of_eq hw'
  let yfin : FiniteAdeleRing (𝓞 L) L := ⟨yfinf, hyfin_int⟩
  let yinf' : InfiniteAdeleRing L := fun w' => (yinf w')⁻¹
  let yfinf' : ∀ w' : HeightOneSpectrum (𝓞 L), w'.adicCompletion L := fun w' => (yfinf w')⁻¹
  have hyfin_int' : ∀ᶠ w' in Filter.cofinite, yfinf' w' ∈ w'.adicCompletionIntegers L := by
    refine hev.mono fun w' hw' => ?_
    rw [mem_adicCompletionIntegers, show yfinf' w' = (yfinf w')⁻¹ from rfl, map_inv₀, hw', inv_one]
  let yfin' : FiniteAdeleRing (𝓞 L) L := ⟨yfinf', hyfin_int'⟩
  have hz0' : ∀ w' : InfinitePlace L, yinf w' ≠ 0 := fun w' => hz0 _ _
  have hY0' : ∀ w' : HeightOneSpectrum (𝓞 L), yfinf w' ≠ 0 := fun w' => hY0 _ _
  let yU : (AdeleRing (𝓞 L) L)ˣ :=
    ⟨(yinf, yfin), (yinf', yfin'),
      Prod.ext (funext fun w' => mul_inv_cancel₀ (hz0' w'))
        (by apply RestrictedProduct.ext; intro w'; exact mul_inv_cancel₀ (hY0' w')),
      Prod.ext (funext fun w' => inv_mul_cancel₀ (hz0' w'))
        (by apply RestrictedProduct.ext; intro w'; exact inv_mul_cancel₀ (hY0' w'))⟩
  refine ⟨yU, Units.ext ?_⟩
  show (M4aHerbrand.GenuineDescent.genuineBaseChange K L).adelicNorm (yinf, yfin) = (u : AdeleRing (𝓞 K) K)
  refine Prod.ext (funext fun v => ?_) ?_
  swap
  ·
    apply RestrictedProduct.ext
    intro v
    refine (P2mS26N0.adelicNorm_snd_apply (K := K) (L := L) _ (yinf, yfin) v).trans
      (Eq.trans (Finset.prod_congr rfl fun w _ => ?_) (hYN v))
    obtain ⟨w', hw'⟩ := w
    subst hw'
    rfl
  ·
    rw [P2mS26N0.adelicNorm_fst_apply (K := K) (L := L), ← hzN v]
    refine Finset.prod_congr rfl fun w _ => ?_
    obtain ⟨w', hw'⟩ := w
    subst hw'
    rfl

theorem mem_range (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ (w : v.Extension (𝓞 L)) (y : w.1.adicCompletion L),
      Algebra.norm (v.adicCompletion K) y = ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)
    (harch : ∀ (v : InfinitePlace K) (hv : v.IsReal),
      (∀ w : InfinitePlace L, w.comap (algebraMap K L) = v → w.IsComplex) →
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) v)) :
    u ∈ B.idelicNorm.range := by
  rw [P2mS26N0.idelicNorm_range_eq (K := K) (L := L) B (M4aHerbrand.GenuineDescent.genuineBaseChange K L)]
  exact mem_range_genuine u hfin harch

end P2mS26N0
p2m_reactivate "P2MW.S_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq.P2mS26N0"

end P2mS26N0Assembly
p2m_reactivate "P2MW.S_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq.P2mS26N0"

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : M4aHerbrand.AdeleBaseChange (NumberField.RingOfIntegers K) K (NumberField.RingOfIntegers L) L)
    (u : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ)
    (hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ (w : v.Extension (NumberField.RingOfIntegers L)) (y : w.1.adicCompletion L),
        Algebra.norm (v.adicCompletion K) y
          = ((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 :
              IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K) v)
    (harch : ∀ (v : NumberField.InfinitePlace K) (hv : v.IsReal),
      (∀ w : NumberField.InfinitePlace L, w.comap (algebraMap K L) = v → w.IsComplex) →
        0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          (((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).1 :
              NumberField.InfiniteAdeleRing K) v)) :
    u ∈ B.idelicNorm.range :=
  P2mS26N0.mem_range B u hfin harch

end S_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq
end P2MW
export P2MW.S_M4aHerbrand_AdeleBaseChange_mem_range_idelicNorm_of_forall_exists_norm_eq (solution)
