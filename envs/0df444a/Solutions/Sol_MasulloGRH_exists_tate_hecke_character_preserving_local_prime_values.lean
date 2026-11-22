-- Prove2me | solution 1 for MasulloGRH.exists_tate_hecke_character_preserving_local_prime_values
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T20:03:32.6013+00:00
-- url     : https://prove2.me/submissions/817dff8c-0af4-46be-9812-3b38d780dbb0

import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MusicOfPrimes_HeckeL
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.UniformRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct
open scoped Topology
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


open NumberField IsDedekindDomain

private theorem phase_make_global_pull
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
    ∃ M : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 F) F)ˣ,
      Continuous M ∧
      (∀ u : Kˣ, M (MasulloGRH.principalIdele K u) =
        MasulloGRH.principalIdele F (Units.map r.symm.toMonoidHom u)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ((e v).adicCompletion K)ˣ),
        M (MasulloGRH.ideleSingle (e v) x) = MasulloGRH.ideleSingle v (l v x) := by
  let H : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 F) F := A.prodMap B
  have hc : Continuous H := (hA.comp continuous_fst).prodMk (hB.comp continuous_snd)
  refine ⟨Units.map H.toMonoidHom, Continuous.units_map _ hc, ?_, ?_⟩
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

private theorem phase_transfer_character {F : Type*} [Field F] [NumberField F]
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
    ∃ η : MusicOfPrimes.HeckeChar K, ∀ v, χ.primeValue v =
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
  refine ⟨η, fun v => ?_⟩
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
theorem solution
    (F : Type*) [Field F] [NumberField F] (K : Type) [Field K] [NumberField K]
    (r : F ≃+* K) (χ : MasulloGRH.HeckeCharacter F) :
    ∃ η : MusicOfPrimes.HeckeChar K, ∀ v : HeightOneSpectrum (𝓞 F),
      let w := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv r) v
      χ.primeValue v =
        if IsUnramifiedCharAt η.toFun w then
          ((η.toFun (uniformizerIdele K w) : ℂˣ) : ℂ) else 0 := by
  classical
  let e := TatePrimeTransport.primeEquiv r
  let g := phase_local_unit_pull r
  obtain ⟨M,hM,hp,hl⟩ := phase_make_global_pull r e (fun v => (g v).toMonoidHom)
    (phase_arch_hom r.symm.toRingHom) (TatePrimeTransport.finitePull r)
    (phase_arch_continuous _) (TatePrimeTransport.finitePull_continuous r)
    (phase_arch_diagonal _) (TatePrimeTransport.finitePull_diagonal r)
    (TatePrimeTransport.finitePull_single r)
  exact phase_transfer_character r χ e M hM hp g hl (phase_local_unit_pull_valuation r)