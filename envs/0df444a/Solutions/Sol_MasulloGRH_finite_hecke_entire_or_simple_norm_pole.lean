-- Prove2me | solution 1 for MasulloGRH.finite_hecke_entire_or_simple_norm_pole
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T20:22:58.494436+00:00
-- url     : https://prove2.me/submissions/ffdd2574-50a4-4ad0-a638-78ab374aed84

import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MasulloGRH_IdeleNorm
import Definitions.Def_MusicOfPrimes_HeckeL
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Data.Countable.Small
import Mathlib.Data.Rat.Encodable
import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.UniformRing
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_sub_mul_eulerProduct_and_eq_mul_prod_Gamma_mul_of_eq_normPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsDedekindDomain Complex
open scoped Classical BigOperators Topology
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open UniformSpace Filter
open scoped Topology WithZero
noncomputable section
namespace TatePrimeTransport
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K] [NumberField F] [NumberField K]

abbrev primeEquiv (r : F ≃+* K) := equivOfRingEquiv (RingOfIntegers.mapRingEquiv r)

theorem intVal (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    (primeEquiv r p).intValuation (RingOfIntegers.mapRingEquiv r x) = p.intValuation x := by
  let e := RingOfIntegers.mapRingEquiv r
  let E : Ideal (𝓞 F) ≃* Ideal (𝓞 K) :=
    { e.idealComapOrderIso.symm.toEquiv with map_mul' := Ideal.map_mul e }
  by_cases hx : x = 0
  · simp [hx]
  have hp : (primeEquiv r p).asIdeal = E p.asIdeal := Ideal.comap_symm e
  have hs : Ideal.span {e x} = E (Ideal.span {x}) := by
    change _ = Ideal.map e _
    rw [Ideal.map_span, Set.image_singleton]
  change (primeEquiv r p).intValuation (e x) = _
  rw [intValuation_eq_exp_neg_multiplicity _ (by simpa using hx),
    intValuation_eq_exp_neg_multiplicity _ hx, hp, hs, multiplicity_map_eq E]

theorem fieldVal (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) (x : F) :
    (primeEquiv r p).valuation K (r x) = p.valuation F x := by
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective (𝓞 F) x
  have he (c : 𝓞 F) : r (algebraMap (𝓞 F) F c) =
      algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv r c) := rfl
  simp only [map_div₀, he, valuation_of_algebraMap, intVal]

private theorem uc {A B : Type*} [Field A] [Field B] [Valued A ℤᵐ⁰] [Valued B ℤᵐ⁰]
    (r : A ≃+* B) (hv : ∀ x, Valued.v (r x) = (Valued.v x : ℤᵐ⁰)) :
    UniformContinuous r := by
  refine uniformContinuous_of_continuousAt_zero r ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨b, hb⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (.ofClass (Valued.v : Valuation B ℤᵐ⁰)) (γ : _)
  change (Valued.v : Valuation B ℤᵐ⁰).restrict b = γ.val at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hb.symm)
  refine ⟨Units.mk0 ((Valued.v : Valuation A ℤᵐ⁰).restrict (r.symm b)) (by simp [hb0]), ?_⟩
  intro x hx
  change (Valued.v : Valuation B ℤᵐ⁰).restrict (r x) < γ.val
  rw [← hb, Valuation.restrict_lt_iff, hv, ← r.apply_symm_apply b, hv]
  exact ((Valued.v : Valuation A ℤᵐ⁰).restrict_lt_iff).mp hx

private abbrev wr (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :=
  WithVal.congr (p.valuation F) ((primeEquiv r p).valuation K) r

private theorem wr_uc (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    UniformContinuous (wr r p) := uc _ (fun x => fieldVal r p x.ofVal)

private theorem wr_uc_inv (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    UniformContinuous (wr r p).symm := uc _ (fun x => by
  change p.valuation F (r.symm x.ofVal) = (primeEquiv r p).valuation K x.ofVal
  simpa using (fieldVal r p (r.symm x.ofVal)).symm)

def localEquiv (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    p.adicCompletion F ≃+* (primeEquiv r p).adicCompletion K :=
  (adicCompletion.equiv F p).trans <|
    (Completion.mapRingEquiv (wr r p) (wr_uc r p).continuous
      (wr_uc_inv r p).continuous).trans (adicCompletion.equiv K (primeEquiv r p)).symm

theorem localEquiv_continuous (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    Continuous (localEquiv r p) :=
  (adicCompletion.continuous_ofCompletion K _).comp
    (Completion.continuous_map.comp (adicCompletion.continuous_toCompletion F p))

theorem localEquiv_symm_continuous (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) :
    Continuous (localEquiv r p).symm :=
  (adicCompletion.continuous_ofCompletion F _).comp
    (Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K _))

theorem localEquiv_coe (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) (x : F) :
    localEquiv r p (algebraMap F _ x) = algebraMap K _ (r x) := by
  apply adicCompletion.ext
  change Completion.map (wr r p) ((WithVal.toVal (p.valuation F) x : WithVal _) : Completion _) = _
  rw [Completion.map_coe (wr_uc r p)]
  rfl

open WithZeroTopology in
theorem localEquiv_valuation (r : F ≃+* K) (p : HeightOneSpectrum (𝓞 F)) (x : p.adicCompletion F) :
    Valued.v (localEquiv r p x) = (Valued.v x : ℤᵐ⁰) := by
  let q := primeEquiv r p
  have hF := Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective F p)
  have hK := Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K q)
  refine (denseRange_algebraMap F p).induction_on (p := fun y => Valued.v (localEquiv r p y) = (Valued.v y : ℤᵐ⁰)) x (isClosed_eq (hK.comp (localEquiv_continuous r p)) hF) ?_
  intro a
  rw [localEquiv_coe]
  exact (adicCompletion.valued_coe K q (r a)).trans
    ((fieldVal r p a).trans (adicCompletion.valued_coe F p a).symm)

end TatePrimeTransport

namespace TatePrimeTransport
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Filter
noncomputable section
variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]

private theorem finitePull_local_mem (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) :
    Set.MapsTo (localEquiv r v).symm
      ((primeEquiv r v).adicCompletionIntegers K : Set _)
      (v.adicCompletionIntegers F : Set _) := by
  intro x hx
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx ⊢
  simpa only [RingEquiv.apply_symm_apply] using
    (localEquiv_valuation r v ((localEquiv r v).symm x)).symm.le.trans
      (by simpa only [RingEquiv.apply_symm_apply] using hx)

def finitePull (r : F ≃+* K) :
    FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (primeEquiv r)
    (primeEquiv r).injective.tendsto_cofinite (fun v => (localEquiv r v).symm.toRingHom)
    (Eventually.of_forall (finitePull_local_mem r))

theorem finitePull_continuous (r : F ≃+* K) : Continuous (finitePull r) := by
  apply RestrictedProduct.mapAlong_continuous _ _ (primeEquiv r) (primeEquiv r).injective.tendsto_cofinite
    (fun v => (localEquiv r v).symm) (Eventually.of_forall (finitePull_local_mem r))
  exact localEquiv_symm_continuous r

theorem finitePull_diagonal (r : F ≃+* K) (z : K) :
    finitePull r (algebraMap K _ z) = algebraMap F _ (r.symm z) := by
  apply Subtype.ext
  funext v
  change (localEquiv r v).symm (algebraMap K _ z) = algebraMap F _ (r.symm z)
  apply (localEquiv r v).injective
  rw [RingEquiv.apply_symm_apply, localEquiv_coe, RingEquiv.apply_symm_apply]

theorem finitePull_single (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F))
    (u : ((primeEquiv r v).adicCompletion K)ˣ) :
    Units.map (finitePull r).toMonoidHom (MasulloGRH.finiteIdeleSingle (primeEquiv r v) u) =
      MasulloGRH.finiteIdeleSingle v (Units.map (localEquiv r v).symm.toMonoidHom u) := by
  classical
  apply Units.ext
  apply Subtype.ext
  funext w
  change (localEquiv r w).symm
    ((RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 K) => (Submonoid.ofClass (v.adicCompletionIntegers K)).units) (primeEquiv r v) u (primeEquiv r w) : ((primeEquiv r w).adicCompletion K)ˣ) : _) =
      ((RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 F) => (Submonoid.ofClass (v.adicCompletionIntegers F)).units) v (Units.map (localEquiv r v).symm.toMonoidHom u) w : (w.adicCompletion F)ˣ) : _)
  by_cases hw : w = v
  · subst w
    rw [RestrictedProduct.mulSingle_eq_same, RestrictedProduct.mulSingle_eq_same]
    rfl
  · have he := (primeEquiv r).injective.ne hw
    rw [RestrictedProduct.mulSingle_eq_of_ne _ _ he, RestrictedProduct.mulSingle_eq_of_ne _ _ hw]
    exact map_one _

end
end TatePrimeTransport

open NumberField IsDedekindDomain TatePrimeTransport

private noncomputable def phase_local_unit_pull {F K : Type*} [Field F] [Field K]
    [NumberField F] [NumberField K] (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) :
    ((primeEquiv r v).adicCompletion K)ˣ ≃* (v.adicCompletion F)ˣ :=
  Units.mapEquiv (localEquiv r v).symm.toMulEquiv

private theorem phase_local_unit_pull_valuation {F K : Type*} [Field F] [Field K]
    [NumberField F] [NumberField K] (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F))
    (x : ((primeEquiv r v).adicCompletion K)ˣ) :
    Valued.v (phase_local_unit_pull r v x : v.adicCompletion F) =
      (Valued.v (x : (primeEquiv r v).adicCompletion K) : ℤᵐ⁰) := by
  change Valued.v ((localEquiv r v).symm x) = _
  simpa only [RingEquiv.apply_symm_apply] using
    (localEquiv_valuation r v ((localEquiv r v).symm x)).symm


open NumberField
open scoped Topology
noncomputable section

private def phase_abs_hom {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) : WithAbs (w.comap r).1 →+* WithAbs w.1 :=
  (WithAbs.equiv w.1).symm.toRingHom.comp (r.comp (WithAbs.equiv (w.comap r).1).toRingHom)

private theorem phase_abs_isometry {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) : Isometry (phase_abs_hom r w) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  exact (InfinitePlace.comap_apply w r _).symm

private def phase_arch_local {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) : (w.comap r).Completion →+* w.Completion :=
  (InfinitePlace.Completion.equiv w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (phase_abs_hom r w) (phase_abs_isometry r w).continuous).comp
      (InfinitePlace.Completion.equiv (w.comap r)).toRingHom)

private theorem phase_arch_local_cont {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) : Continuous (phase_arch_local r w) :=
  (InfinitePlace.Completion.continuous_ofCompletion w).comp
    (UniformSpace.Completion.continuous_map.comp
      (InfinitePlace.Completion.continuous_toCompletion (w.comap r)))

private theorem phase_arch_local_diag {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) (x : F) :
    phase_arch_local r w (algebraMap F (w.comap r).Completion x) = algebraMap K w.Completion (r x) := by
  apply InfinitePlace.Completion.ext
  change (UniformSpace.Completion.mapRingHom (phase_abs_hom r w) (phase_abs_isometry r w).continuous
    (↑((WithAbs.equiv (w.comap r).1).symm x) : (w.comap r).1.Completion)) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

private def phase_arch_hom {F K : Type*} [Field F] [Field K] (r : F →+* K) :
    InfiniteAdeleRing F →+* InfiniteAdeleRing K where
  toFun x w := phase_arch_local r w (x (w.comap r))
  map_zero' := by funext w; exact map_zero _
  map_one' := by funext w; exact map_one _
  map_mul' x y := by funext w; exact map_mul _ _ _
  map_add' x y := by funext w; exact map_add _ _ _

private theorem phase_arch_continuous {F K : Type*} [Field F] [Field K] (r : F →+* K) :
    Continuous (phase_arch_hom r) :=
  continuous_pi (fun w => (phase_arch_local_cont r w).comp (continuous_apply (w.comap r)))

private theorem phase_arch_diagonal {F K : Type*} [Field F] [Field K] (r : F →+* K) (x : F) :
    phase_arch_hom r (algebraMap F (InfiniteAdeleRing F) x) =
      algebraMap K (InfiniteAdeleRing K) (r x) := by
  funext w
  exact phase_arch_local_diag r w x

private theorem phase_arch_inverse {F K : Type*} [Field F] [NumberField F]
    [Field K] [NumberField K] (r : F ≃+* K) :
    Function.LeftInverse (phase_arch_hom r.symm.toRingHom) (phase_arch_hom r.toRingHom) := by
  let : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  intro x
  refine (InfiniteAdeleRing.denseRange_algebraMap F).induction_on x ?_ ?_
  · exact isClosed_eq ((phase_arch_continuous r.symm.toRingHom).comp (phase_arch_continuous r.toRingHom))
      continuous_id
  · intro a
    simp [phase_arch_diagonal]

private def phase_arch_equiv {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) : InfiniteAdeleRing F ≃+* InfiniteAdeleRing K :=
  RingEquiv.ofRingHom (phase_arch_hom r.toRingHom) (phase_arch_hom r.symm.toRingHom)
    (RingHom.ext (phase_arch_inverse r.symm)) (RingHom.ext (phase_arch_inverse r))

private theorem phase_arch_equiv_continuous {F K : Type*} [Field F] [NumberField F]
    [Field K] [NumberField K] (r : F ≃+* K) :
    Continuous (phase_arch_equiv r) ∧ Continuous (phase_arch_equiv r).symm :=
  ⟨phase_arch_continuous r.toRingHom, phase_arch_continuous r.symm.toRingHom⟩

private theorem phase_arch_equiv_diagonal {F K : Type*} [Field F] [NumberField F]
    [Field K] [NumberField K] (r : F ≃+* K) (x : F) :
    phase_arch_equiv r (algebraMap F (InfiniteAdeleRing F) x) =
      algebraMap K (InfiniteAdeleRing K) (r x) :=
  phase_arch_diagonal r.toRingHom x

end

namespace TatePrimeTransport
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
noncomputable section
variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]

theorem finitePull_bijective (r : F ≃+* K) : Function.Bijective (finitePull r) := by
  let e := primeEquiv r
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext w
    obtain ⟨v, rfl⟩ := e.surjective w
    apply (localEquiv r v).symm.injective
    exact congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) hxy
  · intro x
    let g : (v : HeightOneSpectrum (𝓞 F)) → (e v).adicCompletion K :=
      fun v => localEquiv r v (x v)
    let f := Equiv.piCongrLeft (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) e g
    have hfg (v : HeightOneSpectrum (𝓞 F)) : f (e v) = localEquiv r v (x v) :=
      Equiv.piCongrLeft_apply_apply _ _ _ v
    have hint : ∀ᶠ w in cofinite, f w ∈ w.adicCompletionIntegers K := by
      filter_upwards [e.symm.injective.tendsto_cofinite.eventually x.property] with w hw
      obtain ⟨v, rfl⟩ := e.surjective w
      rw [e.symm_apply_apply] at hw
      rw [hfg, mem_adicCompletionIntegers, localEquiv_valuation]
      exact hw
    refine ⟨⟨f, hint⟩, ?_⟩
    apply Subtype.ext
    funext v
    change (localEquiv r v).symm (f (e v)) = x v
    rw [hfg, RingEquiv.symm_apply_apply]

theorem surjective_unit_prodMap (r : F ≃+* K)
    (A : InfiniteAdeleRing K →+* InfiniteAdeleRing F) (hA : Function.Bijective A) :
    Function.Surjective (Units.map (A.prodMap (finitePull r)).toMonoidHom) := by
  let H := A.prodMap (finitePull r)
  have hH : Function.Bijective H := hA.prodMap (finitePull_bijective r)
  let E := RingEquiv.ofBijective H hH
  exact (Units.mapEquiv E.toMulEquiv).surjective

end
end TatePrimeTransport

open NumberField IsDedekindDomain

private theorem pole_global_pull_props
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (e : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 K))
    (l : ∀ v : HeightOneSpectrum (𝓞 F), ((e v).adicCompletion K)ˣ →* (v.adicCompletion F)ˣ)
    (A : InfiniteAdeleRing K →+* InfiniteAdeleRing F)
    (B : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 F) F)
    (hA : Continuous A) (hB : Continuous B)
    (da : ∀ x : K, A (algebraMap K (InfiniteAdeleRing K) x) =
      algebraMap F (InfiniteAdeleRing F) (r.symm x))
    (db : ∀ x : K, B (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (r.symm x))
    (bs : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ((e v).adicCompletion K)ˣ),
      Units.map B.toMonoidHom (MasulloGRH.finiteIdeleSingle (e v) x) =
        MasulloGRH.finiteIdeleSingle v (l v x)) :
    let H : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 F) F := A.prodMap B
    let M := Units.map H.toMonoidHom
    Continuous M ∧
      (∀ u : Kˣ, M (MasulloGRH.principalIdele K u) =
        MasulloGRH.principalIdele F (Units.map r.symm.toMonoidHom u)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ((e v).adicCompletion K)ˣ),
        M (MasulloGRH.ideleSingle (e v) x) = MasulloGRH.ideleSingle v (l v x) := by
  let H : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 F) F := A.prodMap B
  have hc : Continuous H := (hA.comp continuous_fst).prodMk (hB.comp continuous_snd)
  refine ⟨Continuous.units_map _ hc, ?_, ?_⟩
  · intro u
    apply Units.ext
    exact Prod.ext (da u) (db u)
  · intro v x
    apply Units.ext
    refine Prod.ext ?_ ?_
    · exact map_one A
    · exact congrArg Units.val (bs v x)

open NumberField IsDedekindDomain NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open scoped Classical

private theorem phase_single_eq {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    MasulloGRH.ideleSingle v x = Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v x) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · rfl
  refine Subtype.ext (funext fun w => ?_)
  change ((RestrictedProduct.mulSingle
    (fun v : HeightOneSpectrum (𝓞 K) => (Submonoid.ofClass (v.adicCompletionIntegers K)).units)
      v x w : (w.adicCompletion K)ˣ) : w.adicCompletion K) =
    ((localUnit (𝓞 K) K v x : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w
  by_cases h : w = v
  · subst w
    rw [RestrictedProduct.mulSingle_eq_same, localUnit_apply_self]
  · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ h, localUnit_apply_of_ne _ _ _ _ h]
    rfl


open NumberField IsDedekindDomain NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open scoped Classical

private theorem pole_transfer_character {F : Type*} [Field F] [NumberField F]
    {K : Type} [Field K] [NumberField K] (r : F ≃+* K)
    (χ : MasulloGRH.HeckeCharacter F)
    (e : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 K))
    (M : MasulloGRH.IdeleGroup K →* MasulloGRH.IdeleGroup F) (hM : Continuous M)
    (hp : ∀ u : Kˣ, M (MasulloGRH.principalIdele K u) =
      MasulloGRH.principalIdele F (Units.map r.symm.toMonoidHom u))
    (g : ∀ v, ((e v).adicCompletion K)ˣ ≃* (v.adicCompletion F)ˣ)
    (hl : ∀ v x, M (MasulloGRH.ideleSingle (e v) x) = MasulloGRH.ideleSingle v (g v x))
    (hval : ∀ v (x : ((e v).adicCompletion K)ˣ),
      Valued.v ((g v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      Valued.v (x : (e v).adicCompletion K)) :
    ∃ η : MusicOfPrimes.HeckeChar K,
      (∀ y, ((η.toFun y : ℂˣ) : ℂ) = ((χ (QuotientGroup.mk (M y)) : Circle) : ℂ)) ∧
      ∀ v, χ.primeValue v =
      if IsUnramifiedCharAt η.toFun (e v) then
        ((η.toFun (uniformizerIdele K (e v)) : ℂˣ) : ℂ) else 0 := by
  classical
  let q := QuotientGroup.mk' (MasulloGRH.principalIdeles F)
  let C := Circle.toUnits.comp (χ.toMonoidHom.comp (q.comp M))
  have hc : Continuous (fun x => ((C x : ℂˣ) : ℂ)) :=
    continuous_subtype_val.comp (χ.continuous.comp (QuotientGroup.continuous_mk.comp hM))
  have hclass : IsIdeleClassChar (𝓞 K) K C := by
    intro u
    change Circle.toUnits (χ (QuotientGroup.mk (M (MasulloGRH.principalIdele K u)))) = 1
    rw [hp]
    have hm : MasulloGRH.principalIdele F (Units.map r.symm.toMonoidHom u) ∈
        MasulloGRH.principalIdeles F := ⟨_, rfl⟩
    rw [(QuotientGroup.eq_one_iff _).mpr hm, map_one, map_one]
  let η : MusicOfPrimes.HeckeChar K := ⟨C, hc, fun x => Circle.norm_coe _, hclass⟩
  have hloc (v) (x : ((e v).adicCompletion K)ˣ) :
      ((localChar η.toFun (e v) x : ℂˣ) : ℂ) = χ.localComponent v (g v x) := by
    change (χ (QuotientGroup.mk (M (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K (e v) x)))) : ℂ) = _
    rw [← phase_single_eq, hl]
    rfl
  have hun (v) : χ.IsUnramifiedAt v ↔ IsUnramifiedCharAt η.toFun (e v) := by
    constructor
    · intro h x hx hi
      apply Units.ext
      rw [hloc]
      apply h
      rw [hval]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx hi
      rw [Units.val_inv_eq_inv_val, map_inv₀] at hi
      exact le_antisymm hx ((inv_le_one₀
        (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr x.ne_zero))).mp hi)
    · intro h x hx
      let y := (g v).symm x
      have hy : g v y = x := (g v).apply_symm_apply x
      have hyval : Valued.v (y : (e v).adicCompletion K) = 1 := (hval v y).symm.trans (hy ▸ hx)
      have hym : (y : (e v).adicCompletion K) ∈ (e v).adicCompletionIntegers K := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, hyval]
      have hym' : ((y⁻¹ : ((e v).adicCompletion K)ˣ) : (e v).adicCompletion K) ∈
          (e v).adicCompletionIntegers K := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hyval, inv_one]
      rw [←hy, ←hloc, h y hym hym']
      rfl
  refine ⟨η, fun _ => rfl, fun v => ?_⟩
  unfold MasulloGRH.HeckeCharacter.primeValue
  by_cases hu : χ.IsUnramifiedAt v
  · let t := uniformizerUnit K (e v)
    have ht : Valued.v (t : (e v).adicCompletion K) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K _
    have hv : ∃ x : (v.adicCompletion F)ˣ, MasulloGRH.IsUniformizerAt v x :=
      ⟨g v t, (hval v t).trans ht⟩
    rw [dif_pos ⟨hu,hv⟩, if_pos ((hun v).mp hu)]
    let y := (g v).symm hv.choose
    have hy : g v y = hv.choose := (g v).apply_symm_apply _
    have hyval : Valued.v (y : (e v).adicCompletion K) = WithZero.exp (-1 : ℤ) := by
      rw [← hval, hy]
      exact hv.choose_spec
    have hd : Valued.v (((y/t : ((e v).adicCompletion K)ˣ)) : (e v).adicCompletion K) = 1 := by
      change Valued.v ((y : (e v).adicCompletion K)/(t : (e v).adicCompletion K)) = 1
      rw [map_div₀, hyval, ht, div_self WithZero.exp_ne_zero]
    have hn := hu (g v (y/t)) ((hval v (y/t)).trans hd)
    rw [← hloc] at hn
    have hquot : localChar η.toFun (e v) (y/t) = 1 := Units.ext hn
    rw [map_div, div_eq_one] at hquot
    change χ.localComponent v hv.choose = _
    rw [←hy, ←hloc]
    exact congrArg Units.val hquot
  · rw [dif_neg (fun h => hu h.1), if_neg (fun h => hu ((hun v).mpr h))]

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open scoped Classical
private theorem small_number_field_model (F : Type*) [Field F] [NumberField F] :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), Nonempty (F ≃+* K) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  let e := (equivShrink.{0} F).symm
  letI : Field (Shrink.{0} F) := e.field
  let r : Shrink.{0} F ≃+* F := e.ringEquiv
  letI : NumberField (Shrink.{0} F) := NumberField.of_ringEquiv F _ r.symm
  exact ⟨Shrink.{0} F, inferInstance, inferInstance, ⟨r.symm⟩⟩

private theorem angular_tate_primes_norm
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm v.asIdeal =
      Ideal.absNorm ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv r) v).asIdeal) := by
  let R := RingOfIntegers.mapRingEquiv r
  change Nat.card (𝓞 F ⧸ v.asIdeal) =
      Nat.card (𝓞 K ⧸ v.asIdeal.comap (R.symm : 𝓞 K →+* 𝓞 F))
  exact Nat.card_congr (Ideal.quotientEquiv _ _ R (Ideal.comap_symm R)).toEquiv


open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open scoped Classical
private theorem angular_tate_reindex
    {F : Type*} [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F)
    {K : Type} [Field K] [NumberField K] (η : MusicOfPrimes.HeckeChar K)
    (e : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 K))
    (hn : ∀ v, Ideal.absNorm v.asIdeal = Ideal.absNorm (e v).asIdeal)
    (hz : ∀ v, χ.primeValue v =
      if IsUnramifiedCharAt η.toFun (e v) then
        ((η.toFun (uniformizerIdele K (e v)) : ℂˣ) : ℂ) else 0)
    (s : ℂ) :
    MasulloGRH.heckeEulerProduct χ s = MusicOfPrimes.heckeEulerProduct K η s := by
  classical
  unfold MasulloGRH.heckeEulerProduct MusicOfPrimes.heckeEulerProduct
  simpa only [hz, hn] using
    (e.tprod_eq (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (if IsUnramifiedCharAt η.toFun v then
        ((η.toFun (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹))

open NumberField IsDedekindDomain

private noncomputable def poleArchEquiv {F K : Type*} [Field F] [Field K] (r : F ≃+* K) :
    InfinitePlace F ≃ InfinitePlace K where
  toFun w := w.comap r.symm.toRingHom
  invFun w := w.comap r.toRingHom
  left_inv w := by ext x; simp
  right_inv w := by ext x; simp

private theorem poleArchMult {F K : Type*} [Field F] [Field K] (r : F ≃+* K) (w : InfinitePlace F) :
    (poleArchEquiv r w).mult = w.mult := by
  classical
  have hh := InfinitePlace.isReal_comap_iff (w := w) r.symm
  change (if (w.comap r.symm.toRingHom).IsReal then 1 else 2) = if w.IsReal then 1 else 2
  exact if_congr hh rfl rfl

private theorem poleArchLocalNorm {F K : Type*} [Field F] [Field K] (r : F →+* K)
    (w : InfinitePlace K) (x : (w.comap r).Completion) :
    ‖phase_arch_local r w x‖ = ‖x‖ := by
  have hi : Isometry (phase_arch_local r w) := by
    exact ((InfinitePlace.Completion.isometryEquivCompletion w).symm.isometry).comp
      ((phase_abs_isometry r w).completion_map.comp (InfinitePlace.Completion.isometry_toCompletion _))
  simpa using hi.dist_eq x 0

private theorem poleLocalNorm {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) (y : (TatePrimeTransport.primeEquiv r v).adicCompletion K) :
    ‖(TatePrimeTransport.localEquiv r v).symm y‖ = ‖y‖ := by
  rw [FinitePlace.norm_def, FinitePlace.norm_def]
  have hv := (TatePrimeTransport.localEquiv_valuation r v ((TatePrimeTransport.localEquiv r v).symm y)).symm
  rw [RingEquiv.apply_symm_apply] at hv
  rw [hv]
  have hh : Ideal.absNorm v.asIdeal = Ideal.absNorm (TatePrimeTransport.primeEquiv r v).asIdeal :=
    angular_tate_primes_norm r v
  simp only [WithZeroMulInt.toNNReal, hh]

private noncomputable def poleAdelePull {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 F) F :=
  (phase_arch_hom r.symm.toRingHom).prodMap (TatePrimeTransport.finitePull r)

private theorem poleNormCross {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (u : MasulloGRH.IdeleGroup K) :
    MasulloGRH.ideleNorm (Units.map (poleAdelePull r).toMonoidHom u) = MasulloGRH.ideleNorm u := by
  classical
  unfold MasulloGRH.ideleNorm
  congr 1
  · calc
      _ = ∏ w : InfinitePlace F, ‖(u : AdeleRing (𝓞 K) K).1 (poleArchEquiv r w)‖ ^ (poleArchEquiv r w).mult := by
        apply Finset.prod_congr rfl
        intro w _
        rw [poleArchMult]
        exact congrArg (fun t : ℝ => t ^ w.mult) (poleArchLocalNorm r.symm.toRingHom w _)
      _ = _ := (poleArchEquiv r).prod_comp (fun w : InfinitePlace K => ‖(u : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult)
  · calc
      _ = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(u : AdeleRing (𝓞 K) K).2 (TatePrimeTransport.primeEquiv r v)‖ := by
        apply finprod_congr
        intro v
        exact poleLocalNorm r v _
      _ = _ := finprod_comp_equiv (TatePrimeTransport.primeEquiv r) (f := fun v : HeightOneSpectrum (𝓞 K) => ‖(u : AdeleRing (𝓞 K) K).2 v‖)

open NumberField IsDedekindDomain
private theorem angular_pole_norm (K : Type) [Field K] [NumberField K]
    (g : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K g = MasulloGRH.ideleNorm g := by
  unfold NumberField.TateGlobal.ideleNorm MasulloGRH.ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]

open NumberField IsDedekindDomain
private theorem angular_pole_norm_classes
    {F : Type*} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K]
    (χ : MasulloGRH.HeckeCharacter F) (η : MusicOfPrimes.HeckeChar K)
    (M : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hM : Function.Surjective M)
    (hχ : ∀ u : (AdeleRing (𝓞 K) K)ˣ, ((η.toFun u : ℂˣ) : ℂ) =
      ((χ (QuotientGroup.mk (M u)) : Circle) : ℂ))
    (hN : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
      MasulloGRH.ideleNorm (M u) = NumberField.TateGlobal.ideleNorm K u) :
    (¬ χ.IsTrivialOnNormOne → ¬ MusicOfPrimes.IsNormPowChar K η) ∧
    (∀ t : ℝ, χ.IsNormPower t →
      η.toFun = NumberField.TateGlobal.normPowChar K (-t)) := by
  constructor
  · intro hn hη
    apply hn
    obtain ⟨τ,hτ⟩ := hη
    intro g hg
    obtain ⟨u,rfl⟩ := hM g
    apply Subtype.ext
    have hnorm : NumberField.TateGlobal.ideleNorm K u = 1 := (hN u).symm.trans hg
    rw [← hχ u, hτ, NumberField.TateGlobal.coe_normPowChar_apply, hnorm]
    simp
  · intro t ht
    apply MonoidHom.ext
    intro u
    apply Units.ext
    rw [hχ, ht (M u), hN, NumberField.TateGlobal.coe_normPowChar_apply]
    congr 1
    push_cast
    ring

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open scoped Classical

private theorem pole_model (F : Type*) [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (η : MusicOfPrimes.HeckeChar K),
      (∀ s, MasulloGRH.heckeEulerProduct χ s = MusicOfPrimes.heckeEulerProduct K η s) ∧
      (¬χ.IsTrivialOnNormOne → ¬MusicOfPrimes.IsNormPowChar K η) ∧
      ∀ t : ℝ, χ.IsNormPower t → η.toFun = normPowChar K (-t) := by
  obtain ⟨K, kf, kn, ⟨r⟩⟩ := small_number_field_model F
  let e := TatePrimeTransport.primeEquiv r
  let g := phase_local_unit_pull r
  let M := Units.map (poleAdelePull r).toMonoidHom
  have hsurj : Function.Surjective M := TatePrimeTransport.surjective_unit_prodMap r _
    (phase_arch_equiv r.symm).bijective
  obtain ⟨hM,hp,hl⟩ := pole_global_pull_props r e (fun v => (g v).toMonoidHom)
    (phase_arch_hom r.symm.toRingHom) (TatePrimeTransport.finitePull r)
    (phase_arch_continuous _) (TatePrimeTransport.finitePull_continuous r)
    (phase_arch_diagonal _) (TatePrimeTransport.finitePull_diagonal r)
    (TatePrimeTransport.finitePull_single r)
  obtain ⟨η, hm, hz⟩ := pole_transfer_character r χ e M hM hp g hl (phase_local_unit_pull_valuation r)
  refine ⟨K, kf, kn, η, angular_tate_reindex χ η e (angular_tate_primes_norm r) hz, ?_⟩
  apply angular_pole_norm_classes χ η M hsurj hm
  intro u
  exact (poleNormCross r u).trans (angular_pole_norm K u).symm

open Set Filter Complex

private theorem angular_pole_nf_germ (f g : ℂ → ℂ)
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hmatch : ∀ w : ℂ, 1 < w.re → f w = g w) (z : ℂ) :
    f =ᶠ[𝓝[≠] z] g := by
  have hm : MeromorphicOn (f - g) univ := hf.sub hg
  have hseed : meromorphicOrderAt (f - g) (2 : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hright : ∀ᶠ w : ℂ in 𝓝 (2 : ℂ), 1 < w.re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)
    filter_upwards [hright.filter_mono nhdsWithin_le_nhds] with w hw
    exact sub_eq_zero.mpr (hmatch w hw)
  have htop : meromorphicOrderAt (f - g) z = ⊤ := by
    by_contra hn
    exact hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ z) (mem_univ 2) hn hseed
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop] with w hw
  exact sub_eq_zero.mp hw

private theorem angular_pole_nf_entire (L V : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hV : Differentiable ℂ V)
    (hm : ∀ w : ℂ, 1 < w.re → L w = V w) : L = V := by
  funext z
  apply Filter.EventuallyEq.eq_of_nhds
  apply ((hL (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hV.analyticAt z).meromorphicNFAt).1
  exact angular_pole_nf_germ L V (fun w hw => (hL hw).meromorphicAt)
    (fun w _ => (hV.analyticAt w).meromorphicAt) hm z

private theorem angular_pole_nf_polar (L V : ℂ → ℂ) (p : ℂ) (hp : p.re ≤ 1)
    (hL : MeromorphicNFOn L univ) (hV : Differentiable ℂ V)
    (hm : ∀ w : ℂ, 1 < w.re → V w = (w-p) * L w) :
    (∀ z ≠ p, (L =ᶠ[𝓝 z] (fun w => V w / (w-p))) ∧ AnalyticAt ℂ L z) ∧
    (V p ≠ 0 → meromorphicOrderAt L p = -1) := by
  let Q := fun w : ℂ => V w / (w-p)
  have hQ : MeromorphicOn Q univ :=
    fun w _ => (hV.analyticAt w).meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hg (z : ℂ) : L =ᶠ[𝓝[≠] z] Q := by
    apply angular_pole_nf_germ _ _ (fun w hw => (hL hw).meromorphicAt) hQ _ z
    intro w hw
    have hwp : w ≠ p := fun e => (not_lt_of_ge hp) (e ▸ hw)
    exact (eq_div_iff (sub_ne_zero.mpr hwp)).2 (by rw [hm w hw, mul_comm])
  constructor
  · intro z hz
    have hQa : AnalyticAt ℂ Q z :=
      (hV.analyticAt z).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz)
    have he : L =ᶠ[𝓝 z] Q := ((hL (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      hQa.meromorphicNFAt).1 (hg z)
    exact ⟨he, (analyticAt_congr he).2 hQa⟩
  · intro hVp
    rw [meromorphicOrderAt_congr (hg p)]
    change meromorphicOrderAt (V / (fun w => w-p)) p = -1
    have hmden : MeromorphicAt (fun w : ℂ => w-p) p :=
      (analyticAt_id.sub analyticAt_const).meromorphicAt
    rw [meromorphicOrderAt_div (hV.analyticAt p).meromorphicAt hmden,
      (hV.analyticAt p).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 hVp,
      meromorphicOrderAt_id_sub_const, zero_sub]

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm Complex
open Filter Set
open scoped Topology Classical BigOperators

private theorem angular_pole_analytic (F : Type*) [Field F] [NumberField F]
    (K : Type) [Field K] [NumberField K]
    (χ : MasulloGRH.HeckeCharacter F) (η : MusicOfPrimes.HeckeChar K)
    (hP : ∀ w : ℂ, 1 < w.re →
      MasulloGRH.heckeEulerProduct χ w = MusicOfPrimes.heckeEulerProduct K η w)
    (hn : ¬ χ.IsTrivialOnNormOne → ¬ MusicOfPrimes.IsNormPowChar K η)
    (hp : ∀ t : ℝ, χ.IsNormPower t → η.toFun = normPowChar K (-t)) :
    (¬ χ.IsTrivialOnNormOne → Differentiable ℂ (MasulloGRH.heckeLFunction χ)) ∧
    ∀ t : ℝ, χ.IsNormPower t →
      meromorphicOrderAt (MasulloGRH.heckeLFunction χ) (1 + (t : ℂ) * I) = -1 ∧
      ∀ z : ℂ, z ≠ 1 + (t : ℂ) * I → AnalyticAt ℂ (MasulloGRH.heckeLFunction χ) z := by
  classical
  have hcont := MasulloGRH.heckeLFunction_exists_meromorphic_continuation F χ
  have hs : MeromorphicNFOn (MasulloGRH.heckeLFunction χ) Set.univ ∧
      ∀ w : ℂ, 1 < w.re → MasulloGRH.heckeLFunction χ w = MasulloGRH.heckeEulerProduct χ w := by
    unfold MasulloGRH.heckeLFunction
    rw [dif_pos hcont]
    exact hcont.choose_spec
  have hsP (w : ℂ) (hw : 1 < w.re) := (hs.2 w hw).trans (hP w hw)
  constructor
  · intro hx
    let V := MusicOfPrimes.heckeLFinNe K η (hn hx)
    have hV := MusicOfPrimes.heckeLFinNe_spec K η (hn hx)
    rw [angular_pole_nf_entire _ V hs.1 hV.1 (fun w hw => (hsP w hw).trans (hV.2 w hw).symm)]
    exact hV.1
  · intro t hχ
    have ht := hp t hχ
    obtain ⟨V, _, hV, _, hmatch, _⟩ :=
      exists_differentiable_eq_sub_mul_eulerProduct_and_eq_mul_prod_Gamma_mul_of_eq_normPowChar
        K η.toFun η.cont η.unitary η.classChar (MusicOfPrimes.archτ K η)
          (MusicOfPrimes.archm K η) (MusicOfPrimes.archτ_spec K η)
          (MusicOfPrimes.archm_spec K η) (-t) ht
    have hηc : Continuous η.toFun := by
      refine Units.continuous_iff.2 ⟨η.cont, ?_⟩
      simpa only [Function.comp_def, map_inv] using η.cont.comp continuous_inv
    obtain ⟨S, hS⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous K η.toFun hηc
    obtain ⟨c, C, A, hc, _, H⟩ :=
      exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
        K S (localChar η.toFun)
    obtain ⟨_, hpolar⟩ := H η.toFun η.cont η.unitary η.classChar hS (fun _ _ _ _ _ => rfl)
    have hlog : 0 ≤ Real.log (2 + |t + -t|) := Real.log_nonneg (by simp)
    have hne0 := (hpolar (-t) ht V hV hmatch t 1
      (sub_le_self _ (div_nonneg hc.le hlog)) (by norm_num)).1
    have hne : V (1 + (t : ℂ) * I) ≠ 0 := by simpa only [Complex.ofReal_one] using hne0
    have hmatch' (w : ℂ) (hw : 1 < w.re) :
        V w = (w - (1 + (t : ℂ) * I)) * MasulloGRH.heckeLFunction χ w := by
      rw [hsP w hw]
      simpa only [MusicOfPrimes.heckeEulerProduct, Complex.ofReal_neg, neg_mul, sub_neg_eq_add] using hmatch w hw
    have hpol := angular_pole_nf_polar _ _ (1 + (t : ℂ) * I)
      (by simp) hs.1 hV hmatch'
    exact ⟨hpol.2 hne, fun z hz => (hpol.1 z hz).2⟩

open MasulloGRH Complex

theorem solution (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    (¬ χ.IsTrivialOnNormOne → Differentiable ℂ (heckeLFunction χ)) ∧
    ∀ t : ℝ, χ.IsNormPower t →
      meromorphicOrderAt (heckeLFunction χ) (1 + (t : ℂ) * I) = -1 ∧
      ∀ z : ℂ, z ≠ 1 + (t : ℂ) * I → AnalyticAt ℂ (heckeLFunction χ) z := by
  obtain ⟨K, kf, kn, η, hP, hn, hp⟩ := pole_model F χ
  exact angular_pole_analytic F K χ η (fun s _ => hP s) hn hp