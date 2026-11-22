-- Prove2me | solution 1 for MasulloGRH.exists_ideleClassEquiv_and_localEquivs_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T20:37:14.907874+00:00
-- url     : https://prove2.me/submissions/73c4a19b-e121-4ea7-a8d1-3d20f67fc218

-- Adapted from Yi's public Prove2Me submission 3b3443e6 (theorem cd82016f), lines 1-398, 532-617, 743-779.
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
open ComplexConjugate

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

/-! ### Two-way idele class group isomorphism (new; by sflicht) -/

open MasulloGRH NumberField IsDedekindDomain

private theorem icPull_cont {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) : Continuous (poleAdelePull r) :=
  ((phase_arch_continuous r.symm.toRingHom).comp continuous_fst).prodMk
    ((TatePrimeTransport.finitePull_continuous r).comp continuous_snd)

private noncomputable def icIdeleEquiv {F K : Type*} [Field F] [NumberField F] [Field K]
    [NumberField K] (r : F ≃+* K) : IdeleGroup K ≃* IdeleGroup F where
  toFun := Units.map (poleAdelePull r).toMonoidHom
  invFun := Units.map (poleAdelePull r.symm).toMonoidHom
  left_inv y := smooth_iso_inv_units r.symm y
  right_inv x := smooth_iso_inv_units r x
  map_mul' := map_mul _

private theorem icPrincipal {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (u : Kˣ) :
    icIdeleEquiv r (principalIdele K u) = principalIdele F (Units.map r.symm.toMonoidHom u) := by
  apply Units.ext
  exact Prod.ext (phase_arch_diagonal r.symm.toRingHom u) (TatePrimeTransport.finitePull_diagonal r u)

private theorem icPrincipal_map {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) :
    (principalIdeles K).map (icIdeleEquiv r : IdeleGroup K →* IdeleGroup F) = principalIdeles F := by
  ext z
  constructor
  · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
    exact ⟨Units.map r.symm.toMonoidHom u, (icPrincipal r u).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨principalIdele K (Units.map r.toMonoidHom u), ⟨_, rfl⟩, ?_⟩
    change icIdeleEquiv r (principalIdele K (Units.map r.toMonoidHom u)) = _
    rw [icPrincipal]
    congr 1; ext; simp

private noncomputable def icClassEquiv {F K : Type*} [Field F] [NumberField F] [Field K]
    [NumberField K] (r : F ≃+* K) : IdeleClassGroup K ≃ₜ* IdeleClassGroup F where
  toMulEquiv := QuotientGroup.congr (principalIdeles K) (principalIdeles F) (icIdeleEquiv r)
    (icPrincipal_map r)
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk (principalIdeles K)).continuous_iff.mpr
    exact (QuotientGroup.continuous_mk).comp (Continuous.units_map _ (icPull_cont r))
  continuous_invFun := by
    apply (QuotientGroup.isQuotientMap_mk (principalIdeles F)).continuous_iff.mpr
    exact (QuotientGroup.continuous_mk).comp (Continuous.units_map _ (icPull_cont r.symm))

private theorem icClass_mk {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    (r : F ≃+* K) (y : IdeleGroup K) :
    icClassEquiv r (QuotientGroup.mk y) = QuotientGroup.mk (icIdeleEquiv r y) := rfl

theorem solution
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    (e : F ≃+* K) :
    let p := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)
    ∃ (c : IdeleClassGroup F ≃ₜ* IdeleClassGroup K)
      (w : InfinitePlace F ≃ InfinitePlace K)
      (finite : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F ≃+* (p v).adicCompletion K)
      (infinite : ∀ v : InfinitePlace F, v.Completion ≃+* (w v).Completion),
      (∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v (finite v x) = (Valued.v x : ℤᵐ⁰)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ),
        c (QuotientGroup.mk (ideleSingle v x)) =
          QuotientGroup.mk (ideleSingle (p v) (Units.map (finite v).toMonoidHom x))) ∧
      (∀ v : InfinitePlace F, v.IsReal ↔ (w v).IsReal) ∧
      (∀ v : InfinitePlace F, ∃ conjugate : Bool, ∀ x : v.Completion,
        InfinitePlace.Completion.extensionEmbedding (w v) (infinite v x) =
          if conjugate then star (InfinitePlace.Completion.extensionEmbedding v x)
          else InfinitePlace.Completion.extensionEmbedding v x) ∧
      (∀ (v : InfinitePlace F) (x : (v.Completion)ˣ),
        c (QuotientGroup.mk (ideleSingleInfinite v x)) =
          QuotientGroup.mk (ideleSingleInfinite (w v) (Units.map (infinite v).toMonoidHom x))) := by
  intro p
  refine ⟨(icClassEquiv e).symm, poleArchEquiv e, fun v => TatePrimeTransport.localEquiv e v,
    fun w => (sm_local_equiv e w).symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro v x; exact TatePrimeTransport.localEquiv_valuation e v x
  · intro v x
    rw [ContinuousMulEquiv.symm_apply_eq, icClass_mk]
    congr 1
    apply Units.ext
    refine Prod.ext ?_ ?_
    · exact (map_one (phase_arch_hom e.symm.toRingHom)).symm
    · have h := congrArg Units.val (TatePrimeTransport.finitePull_single e v
        (Units.map (TatePrimeTransport.localEquiv e v).toMonoidHom x))
      have hx : Units.map (TatePrimeTransport.localEquiv e v).symm.toMonoidHom
          (Units.map (TatePrimeTransport.localEquiv e v).toMonoidHom x) = x := by
        ext; simp
      rw [hx] at h
      exact h.symm
  · intro v; exact (InfinitePlace.isReal_comap_iff (w := v) e.symm).symm
  · intro w
    rcases sm_orient e w with h | h
    · refine ⟨false, fun x => ?_⟩
      simp only [Bool.false_eq_true, if_false]
      have := h ((sm_local_equiv e w).symm x)
      rw [RingEquiv.apply_symm_apply] at this
      exact this.symm
    · refine ⟨true, fun x => ?_⟩
      simp only [if_true]
      have := h ((sm_local_equiv e w).symm x)
      rw [RingEquiv.apply_symm_apply] at this
      rw [this]; simp
  · intro w x
    rw [ContinuousMulEquiv.symm_apply_eq, icClass_mk]
    congr 1
    change ideleSingleInfinite w x = Units.map (poleAdelePull e).toMonoidHom _
    rw [sm_global_single]
    congr 1; ext; simp
