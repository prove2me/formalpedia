-- Prove2me | solution 1 for MasulloGRH.completedHeckeLFunction_eq_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T20:30:33.650259+00:00
-- url     : https://prove2.me/submissions/3b3443e6-c492-42dc-a668-f2b86e0ff816

import Definitions.Def_MasulloGRH_CompletedL
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.UniformRing
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


private theorem angular_tate_primes_norm
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm v.asIdeal =
      Ideal.absNorm ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv r) v).asIdeal) := by
  let R := RingOfIntegers.mapRingEquiv r
  change Nat.card (𝓞 F ⧸ v.asIdeal) =
      Nat.card (𝓞 K ⧸ v.asIdeal.comap (R.symm : 𝓞 K →+* 𝓞 F))
  exact Nat.card_congr (Ideal.quotientEquiv _ _ R (Ideal.comap_symm R)).toEquiv



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


private noncomputable def poleAdelePull {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 F) F :=
  (phase_arch_hom r.symm.toRingHom).prodMap (TatePrimeTransport.finitePull r)


open NumberField IsDedekindDomain MasulloGRH
open scoped WithZero

private theorem smooth_native_character
    {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
    (r : F ≃+* K) (M : IdeleGroup K →* IdeleGroup F) (hM : Continuous M)
    (hp : ∀ u : Kˣ, M (principalIdele K u) = principalIdele F (Units.map r.symm.toMonoidHom u))
    (χ : HeckeCharacter F) :
    ∃ η : HeckeCharacter K, ∀ y : IdeleGroup K,
      η (QuotientGroup.mk y) = χ (QuotientGroup.mk (M y)) := by
  have hN : principalIdeles K ≤ (principalIdeles F).comap M := by
    rintro _ ⟨u, rfl⟩
    exact ⟨_, (hp u).symm⟩
  let q := QuotientGroup.map (principalIdeles K) (principalIdeles F) M hN
  have hc : Continuous q := by
    apply (QuotientGroup.isQuotientMap_mk (principalIdeles K)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp hM
  exact ⟨PontryaginDual.map (⟨q, hc⟩ : IdeleClassGroup K →ₜ* IdeleClassGroup F) χ, fun _ => rfl⟩

private theorem smooth_native_local_div {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (x y : (v.adicCompletion K)ˣ) :
    χ.localComponent v (x/y) = χ.localComponent v x / χ.localComponent v y := by
  classical
  have hsingle : ideleSingle v (x/y) = ideleSingle v x / ideleSingle v y := by
    have H (a b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        (MulEquiv.prodUnits.symm ((1 : (InfiniteAdeleRing K)ˣ), a/b) : IdeleGroup K) =
        MulEquiv.prodUnits.symm (1,a) / MulEquiv.prodUnits.symm (1,b) := by
      have hx' : ((1 : (InfiniteAdeleRing K)ˣ), a/b) =
          ((1 : (InfiniteAdeleRing K)ˣ), a) / (1,b) := by simp [Prod.div_def]
      rw [hx']
      exact map_div MulEquiv.prodUnits.symm _ _
    unfold ideleSingle finiteIdeleSingle
    rw [RestrictedProduct.mulSingle_div, map_div]
    exact H _ _
  unfold HeckeCharacter.localComponent
  rw [hsingle]
  change ((χ ((QuotientGroup.mk' (principalIdeles K)) (ideleSingle v x / ideleSingle v y)) : Circle) : ℂ) = _
  rw [map_div, map_div, Circle.coe_div]
  rfl

private theorem smooth_native_prime
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (χ : HeckeCharacter F) (η : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (g : (w.adicCompletion K)ˣ ≃* (v.adicCompletion F)ˣ)
    (hval : ∀ x : (w.adicCompletion K)ˣ, Valued.v (g x : v.adicCompletion F) =
      (Valued.v (x : w.adicCompletion K) : ℤᵐ⁰))
    (hl : ∀ x : (w.adicCompletion K)ˣ, η.localComponent w x = χ.localComponent v (g x)) :
    χ.primeValue v = η.primeValue w := by
  let PF := ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x
  let PK := ∃ x : (w.adicCompletion K)ˣ, IsUniformizerAt w x
  have hg : (χ.IsUnramifiedAt v ∧ PF) ↔ (η.IsUnramifiedAt w ∧ PK) := by
    constructor
    · rintro ⟨h, ⟨x,hx⟩⟩
      refine ⟨fun y hy => (hl y).trans (h (g y) ((hval y).trans hy)), g.symm x, ?_⟩
      exact (hval (g.symm x)).symm.trans (by simpa only [MulEquiv.apply_symm_apply, IsUniformizerAt] using hx)
    · rintro ⟨h, ⟨x,hx⟩⟩
      refine ⟨?_, g x, (hval x).trans hx⟩
      intro y hy
      have hv : Valued.v (g.symm y : w.adicCompletion K) = 1 :=
        (hval _).symm.trans (by simpa using hy)
      simpa using (hl (g.symm y)).symm.trans (h _ hv)
  unfold HeckeCharacter.primeValue
  by_cases h : χ.IsUnramifiedAt v ∧ PF
  · have h' := hg.mp h
    rw [dif_pos h, dif_pos h', hl]
    let x := h.2.choose
    let y := g h'.2.choose
    have hx : Valued.v (x : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := h.2.choose_spec
    have hy : Valued.v (y : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := (hval _).trans h'.2.choose_spec
    have hh : Valued.v ((x / y : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      rw [Units.val_div_eq_div_val, map_div₀, hx, hy, div_self WithZero.exp_ne_zero]
    have hdiv := h.1 (x/y) hh
    rw [smooth_native_local_div] at hdiv
    exact (div_eq_one_iff_eq (Circle.coe_ne_zero _)).mp hdiv
  · rw [dif_neg h, dif_neg (fun hk => h (hg.mpr hk))]

private theorem smooth_native_finite
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (χ : HeckeCharacter F) (η : HeckeCharacter K)
    (M : IdeleGroup K →* IdeleGroup F) (hη : ∀ y : IdeleGroup K, η (QuotientGroup.mk y) =
      χ (QuotientGroup.mk (M y)))
    (e : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 K))
    (hn : ∀ v, Ideal.absNorm v.asIdeal = Ideal.absNorm (e v).asIdeal)
    (g : ∀ v, ((e v).adicCompletion K)ˣ ≃* (v.adicCompletion F)ˣ)
    (hl : ∀ v x, M (ideleSingle (e v) x) = ideleSingle v (g v x))
    (hv : ∀ v (x : ((e v).adicCompletion K)ˣ),
      Valued.v (g v x : v.adicCompletion F) = (Valued.v (x : (e v).adicCompletion K) : ℤᵐ⁰)) :
    heckeEulerProduct χ = heckeEulerProduct η ∧ heckeLFunction χ = heckeLFunction η := by
  have hprime (v) : χ.primeValue v = η.primeValue (e v) := by
    apply smooth_native_prime χ η v (e v) (g v) (hv v)
    intro y
    unfold HeckeCharacter.localComponent
    rw [hη, hl]
  have he : heckeEulerProduct χ = heckeEulerProduct η := by
    funext s
    unfold heckeEulerProduct
    simpa only [hprime, hn] using
      (e.tprod_eq (fun w : HeightOneSpectrum (𝓞 K) =>
        (1 - η.primeValue w * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹))
  refine ⟨he, ?_⟩
  unfold heckeLFunction
  rw [he]

open NumberField IsDedekindDomain MasulloGRH

private theorem smooth_native_finite_pair
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (χ : HeckeCharacter F) :
    let M := Units.map (poleAdelePull r).toMonoidHom
    ∃ η : HeckeCharacter K,
      (∀ y : IdeleGroup K, η (QuotientGroup.mk y) = χ (QuotientGroup.mk (M y))) ∧
      (∀ y : IdeleGroup K, η⁻¹ (QuotientGroup.mk y) = χ⁻¹ (QuotientGroup.mk (M y))) ∧
      (heckeEulerProduct χ = heckeEulerProduct η ∧ heckeLFunction χ = heckeLFunction η) ∧
      (heckeEulerProduct χ⁻¹ = heckeEulerProduct η⁻¹ ∧ heckeLFunction χ⁻¹ = heckeLFunction η⁻¹) := by
  let M := Units.map (poleAdelePull r).toMonoidHom
  let e := TatePrimeTransport.primeEquiv r
  let g := phase_local_unit_pull r
  obtain ⟨hM,hp,hl⟩ := pole_global_pull_props r e (fun v => (g v).toMonoidHom)
    (phase_arch_hom r.symm.toRingHom) (TatePrimeTransport.finitePull r)
    (phase_arch_continuous _) (TatePrimeTransport.finitePull_continuous r)
    (phase_arch_diagonal _) (TatePrimeTransport.finitePull_diagonal r)
    (TatePrimeTransport.finitePull_single r)
  obtain ⟨η, hη⟩ := smooth_native_character r M hM hp χ
  have hη' (y : IdeleGroup K) : η⁻¹ (QuotientGroup.mk y) = χ⁻¹ (QuotientGroup.mk (M y)) :=
    congrArg Inv.inv (hη y)
  exact ⟨η, hη, hη', smooth_native_finite χ η M hη e (angular_tate_primes_norm r) g hl
    (phase_local_unit_pull_valuation r), smooth_native_finite χ⁻¹ η⁻¹ M hη' e (angular_tate_primes_norm r) g hl
    (phase_local_unit_pull_valuation r)⟩

set_option backward.isDefEq.respectTransparency.types false
open NumberField IsDedekindDomain MasulloGRH
open scoped ComplexConjugate
noncomputable section

private theorem sm_norm_embedding {F : Type*} [Field F] (w : InfinitePlace F) (x : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ := by
  simpa using (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq x 0

private noncomputable def sm_local_equiv {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]
    (r : F ≃+* K) (w : InfinitePlace F) : (poleArchEquiv r w).Completion ≃+* w.Completion :=
  RingEquiv.ofBijective (phase_arch_local r.symm.toRingHom w) ⟨RingHom.injective _, by
    intro x
    classical
    obtain ⟨v, hv⟩ := (phase_arch_equiv r.symm).surjective (Pi.single w x)
    refine ⟨v (poleArchEquiv r w), ?_⟩
    have hx := congrFun hv w
    change phase_arch_local r.symm.toRingHom w (v (poleArchEquiv r w)) = Pi.single w x w at hx
    rw [Pi.single_eq_same] at hx
    exact hx⟩

private theorem sm_orient {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]
    (r : F ≃+* K) (w : InfinitePlace F) :
    let v := poleArchEquiv r w
    let E := sm_local_equiv r w
    (∀ x, InfinitePlace.Completion.extensionEmbedding w (E x) = InfinitePlace.Completion.extensionEmbedding v x) ∨
    (∀ x, InfinitePlace.Completion.extensionEmbedding w (E x) = conj (InfinitePlace.Completion.extensionEmbedding v x)) := by
  dsimp only
  let v := poleArchEquiv r w
  let A := InfinitePlace.Completion.extensionEmbedding v
  let B := (InfinitePlace.Completion.extensionEmbedding w).comp (sm_local_equiv r w).toRingHom
  have he : InfinitePlace.mk A = InfinitePlace.mk B := by
    ext x
    change ‖A x‖ = ‖(InfinitePlace.Completion.extensionEmbedding w) (phase_arch_local r.symm.toRingHom w x)‖
    exact (sm_norm_embedding v x).trans
      ((sm_norm_embedding w _).trans (poleArchLocalNorm r.symm.toRingHom w x)).symm
  rcases InfinitePlace.mk_eq_iff.mp he with h|h
  · exact Or.inl (fun x => (RingHom.congr_fun h x).symm)
  · exact Or.inr (fun x => (RingHom.congr_fun h x).symm)

private theorem sm_zpow_faithful (m n : ℤ) (h : ∀ z : ℂ, ‖z‖ = 1 → z^m = z^n) : m = n := by
  by_contra hne
  let d := m-n
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  let θ := Real.pi / (d : ℝ)
  let z := Complex.exp ((θ : ℂ)*Complex.I)
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hone : z^d = 1 := by
    rw [show d=m-n from rfl, zpow_sub₀ hz0, h z hz, div_self (zpow_ne_zero _ hz0)]
  have hpow : z^d = -1 := by
    change Complex.exp ((θ : ℂ)*Complex.I)^d = _
    rw [← Complex.exp_int_mul]
    have hθ : (d : ℂ)*((θ : ℂ)*Complex.I) = (Real.pi : ℂ)*Complex.I := by
      dsimp [θ]
      push_cast
      field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast hd]
    rw [hθ, Complex.exp_pi_mul_I]
  rw [hone] at hpow
  norm_num at hpow

private theorem sm_weight_unique {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsComplex) (m n : ℤ)
    (h : ∀ x : w.Completionˣ, ‖(x : w.Completion)‖ = 1 →
      InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) ^m =
        InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) ^n) : m=n := by
  apply sm_zpow_faithful m n
  intro z hz
  obtain ⟨x,hx⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw z
  have hx1 : ‖x‖ = 1 := by simpa only [← hx, sm_norm_embedding] using hz
  have hx0 : x ≠ 0 := by intro h0; simp [h0] at hx1
  simpa only [Units.val_mk0, hx] using h (Units.mk0 x hx0) hx1

private theorem sm_global_single {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]
    (r : F ≃+* K) (w : InfinitePlace F) (x : (poleArchEquiv r w).Completionˣ) :
    Units.map (poleAdelePull r).toMonoidHom (ideleSingleInfinite (poleArchEquiv r w) x) =
      ideleSingleInfinite w (Units.map (sm_local_equiv r w).toMonoidHom x) := by
  classical
  apply Units.ext
  apply Prod.ext
  · funext u
    change phase_arch_local r.symm.toRingHom u
      (((Pi.mulSingle (M := fun a : InfinitePlace K => a.Completionˣ) (poleArchEquiv r w) x (poleArchEquiv r u)) : ((poleArchEquiv r u).Completion)ˣ) : (poleArchEquiv r u).Completion) =
      ((Pi.mulSingle (M := fun a : InfinitePlace F => a.Completionˣ) w (Units.map (sm_local_equiv r w).toMonoidHom x) u : u.Completionˣ) : u.Completion)
    by_cases h : u=w
    · subst u
      simp [sm_local_equiv]
      rfl
    · simp [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne ((poleArchEquiv r).injective.ne h)]
      exact map_one (phase_arch_local r.symm.toRingHom u)
  · exact map_one (TatePrimeTransport.finitePull r)

private def sm_rad {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F) (w : InfinitePlace F) (t : ℝ) :=
  ∀ x : w.Completionˣ, (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
    0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re →
    χ.localComponentInfinite w x = ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ (t*Complex.I)

private def sm_phase {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F) (w : InfinitePlace F) (n : ℤ) :=
  ∀ x : w.Completionˣ, ‖(x : w.Completion)‖ = 1 →
    χ.localComponentInfinite w x = (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)) ^n

private theorem sm_parameters {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]
    (r : F ≃+* K) (w : InfinitePlace F) (χ : HeckeCharacter F) (η : HeckeCharacter K)
    (hm : ∀ x : (poleArchEquiv r w).Completionˣ,
      χ.localComponentInfinite w (Units.map (sm_local_equiv r w).toMonoidHom x) =
      η.localComponentInfinite (poleArchEquiv r w) x) :
    χ.archExponent w = η.archExponent (poleArchEquiv r w) ∧
    χ.archParity w = η.archParity (poleArchEquiv r w) ∧
    (w.IsComplex → χ.archWeight w = η.archWeight (poleArchEquiv r w)) := by
  classical
  let v := poleArchEquiv r w
  let E := sm_local_equiv r w
  let U : v.Completionˣ ≃* w.Completionˣ := Units.mapEquiv E.toMulEquiv
  let A := InfinitePlace.Completion.extensionEmbedding w
  let B := InfinitePlace.Completion.extensionEmbedding v
  have hn (x : v.Completionˣ) : ‖((U x : w.Completionˣ) : w.Completion)‖ = ‖(x : v.Completion)‖ :=
    poleArchLocalNorm r.symm.toRingHom w _
  have hU (x : v.Completionˣ) : χ.localComponentInfinite w (U x) = η.localComponentInfinite v x := hm x
  have hr (x : v.Completionˣ) :
      (A ((U x : w.Completionˣ) : w.Completion)).re = (B (x : v.Completion)).re ∧
      ((A ((U x : w.Completionˣ) : w.Completion)).im = 0 ↔ (B (x : v.Completion)).im = 0) := by
    rcases sm_orient r w with h|h
    · rw [show A ((U x : w.Completionˣ) : w.Completion) = B (x : v.Completion) from h _]
      simp
    · rw [show A ((U x : w.Completionˣ) : w.Completion) = conj (B (x : v.Completion)) from h _]
      simp
  have hrad : sm_rad χ w = sm_rad η v := by
    funext t
    apply propext
    constructor
    · intro h x hi hp
      rw [← hU]
      rw [h _ ((hr x).2.mpr hi) ((hr x).1.symm ▸ hp), hn, poleArchMult]
    · intro h y hi hp
      obtain ⟨x, rfl⟩ := U.surjective y
      rw [hU, hn, ← poleArchMult r w]
      exact h _ ((hr x).2.mp hi) ((hr x).1 ▸ hp)
  have hExp : χ.archExponent w = η.archExponent v := by
    let pick := fun p : ℝ → Prop => if h : ∃ t, p t then h.choose else 0
    exact congrArg pick hrad
  have hPar : χ.archParity w = η.archParity v := by
    have h := hm (-1)
    have hneg : Units.map (sm_local_equiv r w).toMonoidHom (-1) = -1 := by
      apply Units.ext
      change (sm_local_equiv r w) (-1) = -1
      simp
    rw [hneg] at h
    simp only [HeckeCharacter.archParity, h, v]
  refine ⟨hExp, hPar, fun hw => ?_⟩
  have hv : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp (fun h =>
    (InfinitePlace.not_isReal_iff_isComplex.mpr hw) ((InfinitePlace.isReal_comap_iff r.symm).mp h))
  have huniq (a b : ℤ) (ha : sm_phase η v a) (hb : sm_phase η v b) : a=b :=
    sm_weight_unique v hv a b (fun x hx => (ha x hx).symm.trans (hb x hx))
  let pick := fun p : ℤ → Prop => if h : ∃ n, p n then h.choose.natAbs else 0
  change pick (sm_phase χ w) = pick (sm_phase η v)
  rcases sm_orient r w with ho|ho
  · apply congrArg pick
    funext n
    apply propext
    constructor
    · intro h x hx
      rw [← hU, h _ ((hn x).trans hx)]
      exact congrArg (· ^n) (ho _)
    · intro h y hy
      obtain ⟨x, rfl⟩ := U.surjective y
      rw [hU, h _ ((hn x).symm.trans hy)]
      exact congrArg (· ^n) (ho _).symm
  · have hphase (n : ℤ) : sm_phase χ w n ↔ sm_phase η v (-n) := by
      have hpow (x : v.Completionˣ) (hx : ‖(x : v.Completion)‖ = 1) :
          A ((U x : w.Completionˣ) : w.Completion) ^n = B (x : v.Completion)^(-n) := by
        rw [show A ((U x : w.Completionˣ) : w.Completion) = conj (B (x : v.Completion)) from ho _,
          ← Complex.inv_eq_conj (show ‖B (x : v.Completion)‖ = 1 from (sm_norm_embedding v _).trans hx),
          inv_zpow, zpow_neg]
      constructor
      · intro h x hx
        rw [← hU, h _ ((hn x).trans hx)]
        exact hpow x hx
      · intro h y hy
        obtain ⟨x, rfl⟩ := U.surjective y
        rw [hU, h _ ((hn x).symm.trans hy)]
        exact (hpow x ((hn x).symm.trans hy)).symm
    by_cases hF : ∃ n, sm_phase χ w n
    · have hK : ∃ n, sm_phase η v n := ⟨-hF.choose, (hphase _).mp hF.choose_spec⟩
      simp only [pick, dif_pos hF, dif_pos hK]
      rw [huniq hK.choose (-hF.choose) hK.choose_spec ((hphase _).mp hF.choose_spec), Int.natAbs_neg]
    · have hK : ¬ ∃ n, sm_phase η v n := by
        rintro ⟨k,hk⟩
        exact hF ⟨-k, (hphase _).mpr (by simpa using hk)⟩
      simp [pick, hF, hK]

private theorem smooth_arch_transport_gamma {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]
    (r : F ≃+* K) (χ : HeckeCharacter F) (η : HeckeCharacter K)
    (hm : ∀ y : IdeleGroup K, η (QuotientGroup.mk y) =
      χ (QuotientGroup.mk (Units.map (poleAdelePull r).toMonoidHom y))) (s : ℂ) :
    χ.gammaFactor s = η.gammaFactor s := by
  classical
  unfold HeckeCharacter.gammaFactor
  rw [← (poleArchEquiv r).prod_comp (fun v => η.archLFactor v s)]
  apply Finset.prod_congr rfl
  intro w _
  have hloc (x : (poleArchEquiv r w).Completionˣ) :
      χ.localComponentInfinite w (Units.map (sm_local_equiv r w).toMonoidHom x) =
      η.localComponentInfinite (poleArchEquiv r w) x := by
    unfold HeckeCharacter.localComponentInfinite
    rw [hm, sm_global_single]
  obtain ⟨hx, hp, hw⟩ := sm_parameters r w χ η hloc
  have hre : (poleArchEquiv r w).IsReal ↔ w.IsReal := InfinitePlace.isReal_comap_iff r.symm
  by_cases hReal : w.IsReal
  · simp only [HeckeCharacter.archLFactor, hReal, hre.mpr hReal, if_true, hx, hp]
  · simp only [HeckeCharacter.archLFactor, if_neg hReal, if_neg (hReal ∘ hre.mp), hx,
      hw (InfinitePlace.not_isReal_iff_isComplex.mp hReal)]

end

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TatePrimeTransport MasulloGRH

private theorem smooth_iso_inv_coordinate {F : Type*} [Field F] [NumberField F]
    (u v : HeightOneSpectrum (𝓞 F)) (huv : u = v)
    (B : u.adicCompletion F →+* v.adicCompletion F) (hc : Continuous B)
    (hdiag : ∀ t : F, B (algebraMap F _ t) = algebraMap F _ t)
    (x : FiniteAdeleRing (𝓞 F) F) : B (x u) = x v := by
  subst u
  exact (denseRange_algebraMap F v).induction_on (p := fun z => B z = z) (x v)
    (isClosed_eq hc continuous_id) hdiag

private theorem smooth_iso_inv_finite {F K : Type*} [Field F] [Field K]
    [NumberField F] [NumberField K] (r : F ≃+* K) (x : FiniteAdeleRing (𝓞 F) F) :
    finitePull r (finitePull r.symm x) = x := by
  apply Subtype.ext
  funext v
  let w := primeEquiv r v
  let u := primeEquiv r.symm w
  have huv : u = v := by
    exact (primeEquiv r).symm_apply_apply v
  let B := (localEquiv r v).symm.toRingHom.comp (localEquiv r.symm w).symm.toRingHom
  apply smooth_iso_inv_coordinate u v huv B
      ((localEquiv_symm_continuous r v).comp (localEquiv_symm_continuous r.symm w))
  intro a
  have h := congrArg (fun t : FiniteAdeleRing (𝓞 F) F => t v)
    (show finitePull r (finitePull r.symm (algebraMap F _ a)) = algebraMap F _ a by
      rw [finitePull_diagonal, finitePull_diagonal]; simp)
  exact h

private theorem smooth_iso_inv_adele {F K : Type*} [Field F] [Field K]
    [NumberField F] [NumberField K] (r : F ≃+* K) (x : AdeleRing (𝓞 F) F) :
    poleAdelePull r (poleAdelePull r.symm x) = x := by
  exact Prod.ext (phase_arch_inverse r x.1) (smooth_iso_inv_finite r x.2)

private theorem smooth_iso_inv_units {F K : Type*} [Field F] [Field K]
    [NumberField F] [NumberField K] (r : F ≃+* K) (y : IdeleGroup F) :
    Units.map (poleAdelePull r).toMonoidHom
      (Units.map (poleAdelePull r.symm).toMonoidHom y) = y := by
  exact Units.ext (smooth_iso_inv_adele r y.val)

open MasulloGRH NumberField

private theorem smooth_iso_char_ext {F : Type*} [Field F] [NumberField F]
    {χ η : HeckeCharacter F}
    (h : ∀ y : IdeleGroup F, χ (QuotientGroup.mk y) = η (QuotientGroup.mk y)) : χ = η := by
  apply PontryaginDual.ext
  intro a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  exact h y

private theorem smooth_iso_char_equiv
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (M : IdeleGroup K →* IdeleGroup F) (N : IdeleGroup F →* IdeleGroup K)
    (hMN : ∀ x, M (N x) = x) (hNM : ∀ y, N (M y) = y)
    (forward : ∀ χ : HeckeCharacter F, ∃ η : HeckeCharacter K, ∀ y : IdeleGroup K,
      η (QuotientGroup.mk y) = χ (QuotientGroup.mk (M y)))
    (backward : ∀ η : HeckeCharacter K, ∃ χ : HeckeCharacter F, ∀ x : IdeleGroup F,
      χ (QuotientGroup.mk x) = η (QuotientGroup.mk (N x))) :
    ∃ tr : HeckeCharacter F ≃* HeckeCharacter K,
      (∀ χ (y : IdeleGroup K), tr χ (QuotientGroup.mk y) = χ (QuotientGroup.mk (M y))) ∧
      (∀ η (x : IdeleGroup F), tr.symm η (QuotientGroup.mk x) = η (QuotientGroup.mk (N x))) := by
  classical
  let T := fun χ => (forward χ).choose
  let S := fun η => (backward η).choose
  have hT (χ : HeckeCharacter F) (y : IdeleGroup K) :
      T χ (QuotientGroup.mk y) = χ (QuotientGroup.mk (M y)) := (forward χ).choose_spec y
  have hS (η : HeckeCharacter K) (x : IdeleGroup F) :
      S η (QuotientGroup.mk x) = η (QuotientGroup.mk (N x)) := (backward η).choose_spec x
  let tr : HeckeCharacter F ≃* HeckeCharacter K :=
    { toFun := T
      invFun := S
      left_inv := fun χ => smooth_iso_char_ext fun x => by rw [hS, hT, hMN]
      right_inv := fun η => smooth_iso_char_ext fun y => by rw [hT, hS, hNM]
      map_mul' := fun χ ψ => smooth_iso_char_ext fun y => by
        change T (χ*ψ) (QuotientGroup.mk y) = T χ (QuotientGroup.mk y) * T ψ (QuotientGroup.mk y)
        rw [hT, hT, hT]
        rfl }
  exact ⟨tr, hT, hS⟩

open MasulloGRH NumberField

private theorem smooth_iso_char_pair
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K)
    (hMN : ∀ x : IdeleGroup F, Units.map (poleAdelePull r).toMonoidHom
      (Units.map (poleAdelePull r.symm).toMonoidHom x) = x)
    (hNM : ∀ y : IdeleGroup K, Units.map (poleAdelePull r.symm).toMonoidHom
      (Units.map (poleAdelePull r).toMonoidHom y) = y) :
    let M := Units.map (poleAdelePull r).toMonoidHom
    let N := Units.map (poleAdelePull r.symm).toMonoidHom
    ∃ tr : HeckeCharacter F ≃* HeckeCharacter K,
      (∀ χ (y : IdeleGroup K), tr χ (QuotientGroup.mk y) = χ (QuotientGroup.mk (M y))) ∧
      (∀ η (x : IdeleGroup F), tr.symm η (QuotientGroup.mk x) = η (QuotientGroup.mk (N x))) := by
  apply smooth_iso_char_equiv _ _ hMN hNM
  · intro χ
    obtain ⟨η, h, _⟩ := smooth_native_finite_pair r χ
    exact ⟨η,h⟩
  · intro η
    obtain ⟨χ, h, _⟩ := smooth_native_finite_pair r.symm η
    exact ⟨χ,h⟩

open NumberField MasulloGRH

private theorem smooth_iso_match_completion
    {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (tr : HeckeCharacter F ≃* HeckeCharacter K)
    (htr : ∀ (χ : HeckeCharacter F) (y : IdeleGroup K), tr χ (QuotientGroup.mk y) =
      χ (QuotientGroup.mk (Units.map (poleAdelePull r).toMonoidHom y))) (χ : HeckeCharacter F) :
    completedHeckeLFunction χ = completedHeckeLFunction (tr χ) := by
  obtain ⟨η, hη, _, ⟨_, hf⟩, _⟩ := smooth_native_finite_pair r χ
  have h : tr χ = η := by
    apply PontryaginDual.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact (htr χ y).trans (hη y).symm
  rw [h]
  unfold completedHeckeLFunction
  rw [hf, show χ.gammaFactor = η.gammaFactor from funext (smooth_arch_transport_gamma r χ η hη)]

theorem solution
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    (e : F ≃+* K) :
    ∃ transport : HeckeCharacter F ≃* HeckeCharacter K,
      ∀ χ : HeckeCharacter F,
        completedHeckeLFunction χ = completedHeckeLFunction (transport χ) := by
  obtain ⟨tr, ht, _⟩ := smooth_iso_char_pair e (smooth_iso_inv_units e) (smooth_iso_inv_units e.symm)
  exact ⟨tr, smooth_iso_match_completion e tr ht⟩
