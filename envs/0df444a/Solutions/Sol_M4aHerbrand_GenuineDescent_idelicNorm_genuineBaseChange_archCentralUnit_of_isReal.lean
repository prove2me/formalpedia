-- Prove2me | solution 1 for M4aHerbrand.GenuineDescent.idelicNorm_genuineBaseChange_archCentralUnit_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ffb17459-00b7-576b-9be6-b110e7abdb27

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_GenuineDescent_idelicNorm_genuineBaseChange_archCentralUnit_of_isReal
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Ws23
namespace NArch

open NumberField IsDedekindDomain M4aHerbrand
open scoped TensorProduct

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

theorem piMap_apply (f : ∀ i, M i →ₗ[R] M i) (x : ∀ i, M i) (i : ι) :
    piMap f x i = f i (x i) :=
  rfl

attribute [local simp] piMap_apply

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

end Arch

end A

section RealNorm

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver

theorem norm_ringEquivRealOfIsReal_symm {K L : Type*} [Field K] [Field L] [Algebra K L]
    {v : InfinitePlace K} {w : InfinitePlace L} [w.1.LiesOver v.1]
    (hv : v.IsReal) (hw : w.IsReal) (t : ℝ) :
    Algebra.norm v.Completion ((ringEquivRealOfIsReal hw).symm t) = (ringEquivRealOfIsReal hv).symm t := by
  have := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
  rw [Algebra.norm_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal hw)
      (RingHom.ext fun _ => Complex.ofReal_inj.1 <| by simp) ((ringEquivRealOfIsReal hw).symm t),
    RingEquiv.apply_symm_apply, Algebra.norm_self, MonoidHom.id_apply]

end RealNorm

end Ws23.NArch

end

open NumberField M4aHerbrand M4aHerbrand.GenuineDescent AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (x : ℝˣ) :
    (genuineBaseChange ℚ K).idelicNorm
        (AdelicVolume.archCentralUnit K w
          (Units.mapEquiv (ringEquivRealOfIsReal hw).symm.toMulEquiv x)) =
      AdelicVolume.archCentralUnit ℚ Rat.infinitePlace
        (Units.mapEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toMulEquiv x) := by
  classical
  apply Units.ext
  show (genuineBaseChange ℚ K).adelicNorm
      ((AdelicVolume.archCentralUnit K w
          (Units.mapEquiv (ringEquivRealOfIsReal hw).symm.toMulEquiv x) : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K) =
    ((AdelicVolume.archCentralUnit ℚ Rat.infinitePlace
        (Units.mapEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toMulEquiv x) :
          (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)
  refine Prod.ext ?_ ?_
  ·
    funext v
    obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
    rw [Ws23.NArch.adelicNorm_fst_apply ℚ K _ Rat.infinitePlace,
      AdelicVolume.archCentralUnit_fst_self]
    have hwext : w.comap (algebraMap ℚ K) = Rat.infinitePlace := Subsingleton.elim _ _
    rw [Finset.prod_eq_single (⟨w, hwext⟩ : (Rat.infinitePlace).Extension K)]
    · rw [AdelicVolume.archCentralUnit_fst_self]
      haveI : w.1.LiesOver (Rat.infinitePlace).1 := M4aHerbrand.ArchSemilocal.liesOver_of_comap_eq hwext
      exact Ws23.NArch.norm_ringEquivRealOfIsReal_symm Rat.isReal_infinitePlace hw (x : ℝ)
    · intro w' _ hw'
      have hne : w'.1 ≠ w := fun h => hw' (Subtype.ext h)
      rw [AdelicVolume.archCentralUnit_fst_of_ne w _ hne, map_one]
    · intro h
      exact (h (@Finset.mem_univ _ (_) _)).elim
  ·
    rw [AdelicVolume.archCentralUnit_snd]
    have hN : ∀ y : AdeleRing (𝓞 K) K, (genuineBaseChange ℚ K).adelicNorm y =
        (letI := (M4aHerbrand.Bridge.genuineβ ℚ K).toAlgebra; Algebra.norm (AdeleRing (𝓞 ℚ) ℚ) y) :=
      fun _ => rfl
    rw [hN]
    apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
    intro p
    letI : Fintype (p.Extension (𝓞 K)) :=
      IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    rw [(M4aHerbrand.genuineAdelicNorm_componentwise ℚ K _).2 p]
    rw [Finset.prod_eq_one (fun w' _ => by
      rw [AdelicVolume.archCentralUnit_snd]
      exact map_one _)]
    rfl

end S_M4aHerbrand_GenuineDescent_idelicNorm_genuineBaseChange_archCentralUnit_of_isReal
end P2MW
export P2MW.S_M4aHerbrand_GenuineDescent_idelicNorm_genuineBaseChange_archCentralUnit_of_isReal (solution)
