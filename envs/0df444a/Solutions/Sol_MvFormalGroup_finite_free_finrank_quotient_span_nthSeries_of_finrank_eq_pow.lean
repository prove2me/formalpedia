-- Prove2me | solution 1 for MvFormalGroup.finite_free_finrank_quotient_span_nthSeries_of_finrank_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/cee34c91-26be-5b67-bdaf-c420cddd6f0e

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_Patching_SystemTypes
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal
import Theorems.Thm_IsRegularLocalRing_mvPowerSeries_fin
import Theorems.Thm_MvPowerSeries_depth_self_eq_ringKrullDim_fin_of_isDiscreteValuationRing
import Theorems.Thm_MvPowerSeries_depth_self_fin_eq_of_isDiscreteValuationRing
import Theorems.Thm_IsLocalRing_isRegular_of_systemOfParameters
import Theorems.Thm_Module_free_of_quotSMulTop_free
import Theorems.Thm_Module_finrank_quotSMulTop_eq
import Theorems.Thm_Module_Finite_of_isAdicComplete_of_isHausdorff_of_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_finite_free_finrank_quotient_span_nthSeries_of_finrank_eq_pow

set_option autoImplicit false

open MvPowerSeries
open scoped Pointwise

universe u v

namespace LevelFree

section FGL

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {d : ℕ}

private theorem constantCoeff_nthSeries (F : MvFormalGroup d R) (n : ℕ) (i : Fin d) :
    (F.nthSeries n i).constantCoeff = 0 := by
  induction n generalizing i with
  | zero => simp [MvFormalGroup.nthSeries_zero]
  | succ n ih =>
    rw [MvFormalGroup.nthSeries_succ]
    have hz : ∀ s : Fin d ⊕ Fin d,
        (Sum.elim (F.nthSeries n) (fun j => (X j : MvPowerSeries (Fin d) R)) s).constantCoeff = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hz) hz (F.constantCoeff_eq_zero i)

private theorem nthSeries_map (f : R →+* S) (F : MvFormalGroup d R) (n : ℕ) :
    (F.map f).nthSeries n = fun i => MvPowerSeries.map f (F.nthSeries n i) := by
  induction n with
  | zero => funext i; simp [MvFormalGroup.nthSeries_zero]
  | succ n ih =>
    funext i
    have hz : ∀ s : Fin d ⊕ Fin d,
        (Sum.elim (F.nthSeries n) (fun j => (X j : MvPowerSeries (Fin d) R)) s).constantCoeff = 0 := by
      rintro (j | j)
      · exact constantCoeff_nthSeries F n j
      · exact constantCoeff_X _
    have ha := hasSubst_of_constantCoeff_zero hz
    rw [MvFormalGroup.nthSeries_succ, MvFormalGroup.nthSeries_succ, ih]
    change subst _ (MvPowerSeries.map f (F.toPowerSeries i)) = _
    rw [map_subst ha]
    congr 1
    funext s
    rcases s with j | j
    · rfl
    · simp [map_X]

end FGL

section Reduction

variable {𝓞 : Type u} [CommRing 𝓞] (ϖ : 𝓞) {d : ℕ}

private noncomputable def red :
    MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {ϖ}) :=
  MvPowerSeries.mapAlgHom (σ := Fin d) (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {ϖ}))

private theorem red_apply (G : MvPowerSeries (Fin d) 𝓞) :
    red ϖ G = MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) G := rfl

private theorem red_surjective : Function.Surjective (red (d := d) ϖ) := by
  intro G
  refine ⟨fun n => (Ideal.Quotient.mk_surjective (G n)).choose, ?_⟩
  ext n
  rw [red_apply, coeff_map]
  exact (Ideal.Quotient.mk_surjective (G n)).choose_spec

private theorem ker_red :
    RingHom.ker (red (d := d) ϖ) = Ideal.span {(C ϖ : MvPowerSeries (Fin d) 𝓞)} := by
  apply le_antisymm
  · intro G hG
    rw [RingHom.mem_ker, red_apply] at hG
    have hc : ∀ n : Fin d →₀ ℕ, ∃ c : 𝓞, c * ϖ = coeff n G := fun n => by
      have := congrArg (coeff n) hG
      rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem] at this
      exact Ideal.mem_span_singleton'.1 this
    choose c hc using hc
    let H : MvPowerSeries (Fin d) 𝓞 := fun n => c n
    refine Ideal.mem_span_singleton'.2 ⟨H, ?_⟩
    ext n
    rw [mul_comm, coeff_C_mul, mul_comm]
    exact hc n
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, red_apply, map_C,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ), map_zero]

variable (f : Fin d → MvPowerSeries (Fin d) 𝓞)

private noncomputable def redQuot :
    MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞]
      MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {ϖ}) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f i)) :=
  (Ideal.Quotient.mkₐ 𝓞 _).comp (red ϖ)

private theorem redQuot_surjective : Function.Surjective (redQuot ϖ f) :=
  (Ideal.Quotient.mkₐ_surjective 𝓞 _).comp (red_surjective ϖ)

private theorem ker_redQuot :
    RingHom.ker (redQuot ϖ f) =
      Ideal.span (Set.range f) ⊔ Ideal.span {(C ϖ : MvPowerSeries (Fin d) 𝓞)} := by
  have h1 : Ideal.span (Set.range fun i => MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f i)) =
      Ideal.map (red (d := d) ϖ) (Ideal.span (Set.range f)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  ext G
  rw [RingHom.mem_ker, redQuot, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, h1,
    ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective ϖ), ← RingHom.ker_eq_comap_bot, ker_red]

private noncomputable def levelRed :
    (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range f)) →ₐ[𝓞]
      MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {ϖ}) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f i)) :=
  Ideal.Quotient.liftₐ _ (redQuot ϖ f) fun a ha => by
    rw [← RingHom.mem_ker, ker_redQuot]
    exact Ideal.mem_sup_left ha

private theorem levelRed_mk (G : MvPowerSeries (Fin d) 𝓞) :
    levelRed ϖ f (Ideal.Quotient.mk _ G) = redQuot ϖ f G := rfl

private theorem smul_mk (H : MvPowerSeries (Fin d) 𝓞) :
    ϖ • (Ideal.Quotient.mk (Ideal.span (Set.range f)) H) = Ideal.Quotient.mk _ (C ϖ * H) := by
  rw [← smul_eq_C_mul]
  exact (map_smul (Ideal.Quotient.mkₐ 𝓞 (Ideal.span (Set.range f))) ϖ H).symm

private theorem levelRed_surjective : Function.Surjective (levelRed ϖ f) := by
  intro y
  obtain ⟨G, rfl⟩ := redQuot_surjective ϖ f y
  exact ⟨Ideal.Quotient.mk _ G, rfl⟩

private theorem levelRed_eq_zero_iff (x : MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range f)) :
    levelRed ϖ f x = 0 ↔ ∃ y, x = ϖ • y := by
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [levelRed_mk, ← RingHom.mem_ker, ker_redQuot]
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, smul_mk, mul_comm]
  · rintro ⟨y, hy⟩
    obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [smul_mk, Ideal.Quotient.eq] at hy
    have : G = (G - C ϖ * H) + C ϖ * H := by ring
    rw [this]
    exact Submodule.add_mem_sup hy (Ideal.mem_span_singleton'.2 ⟨H, mul_comm _ _⟩)

private theorem ker_levelRed_toLinearMap :
    LinearMap.ker (levelRed ϖ f).toLinearMap =
      ϖ • (⊤ : Submodule 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range f))) := by
  ext x
  rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, levelRed_eq_zero_iff, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩

private noncomputable def quotSMulTopEquiv :
    QuotSMulTop ϖ (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range f)) ≃ₗ[𝓞]
      MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {ϖ}) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f i)) :=
  Submodule.quotEquivOfEq _ _ (ker_levelRed_toLinearMap ϖ f).symm ≪≫ₗ
    (levelRed ϖ f).toLinearMap.quotKerEquivOfSurjective (levelRed_surjective ϖ f)

private noncomputable def quotSMulTopEquiv' :
    QuotSMulTop ϖ (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range f)) ≃ₗ[𝓞 ⧸ Ideal.span {ϖ}]
      MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {ϖ}) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f i)) :=
  { quotSMulTopEquiv ϖ f with
    map_smul' := fun c x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      change quotSMulTopEquiv ϖ f (Ideal.Quotient.mk _ a • x) = Ideal.Quotient.mk _ a • quotSMulTopEquiv ϖ f x
      rw [Module.IsTorsionBy.mk_smul (Module.isTorsionBy_quotient_element_smul _ ϖ), map_smul]
      exact (IsScalarTower.algebraMap_smul (𝓞 ⧸ Ideal.span {ϖ}) a _).symm }

private noncomputable def quotSupEquiv :
    (MvPowerSeries (Fin d) 𝓞 ⧸ (Ideal.span (Set.range f) ⊔ Ideal.span {(C ϖ : MvPowerSeries (Fin d) 𝓞)})) ≃+*
      MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {ϖ}) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f i)) :=
  (Ideal.quotEquivOfEq (ker_redQuot ϖ f).symm).trans
    (RingHom.quotientKerEquivOfSurjective (redQuot_surjective ϖ f))

end Reduction

section Main

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] {d : ℕ}

local notation "𝔸" => MvPowerSeries (Fin d) 𝓞
local notation "𝕜" => 𝓞 ⧸ Ideal.span {(p : 𝓞)}

private theorem main (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (F : MvFormalGroup d 𝓞) (h v : ℕ)
    (hrk : Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((F.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries (p ^ v)))) =
      p ^ (v * h)) :
    Module.Finite 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) ∧
    Module.Free 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) ∧
    Module.finrank 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) =
      p ^ (v * h) := by
  classical

  obtain ⟨hD, hDVR, -, hmax⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal (𝓞 := 𝓞) p hp
  have hpm : (p : 𝓞) ∈ IsLocalRing.maximalIdeal 𝓞 := by
    rw [hmax]; exact Ideal.mem_span_singleton_self _
  have hpu : ¬ IsUnit (p : 𝓞) := (IsLocalRing.mem_maximalIdeal _).1 hpm
  have hp0 : 0 < p ^ (v * h) := pow_pos (Fact.out : p.Prime).pos _
  letI : Field 𝕜 := Ideal.Quotient.field _

  rw [nthSeries_map] at hrk
  haveI : Module.Finite 𝕜 (MvPowerSeries (Fin d) 𝕜 ⧸ Ideal.span (Set.range fun i =>
      MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) (F.nthSeries (p ^ v) i))) :=
    Module.finite_of_finrank_pos (by rw [hrk]; exact hp0)
  haveI : Nontrivial (MvPowerSeries (Fin d) 𝕜 ⧸ Ideal.span (Set.range fun i =>
      MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) (F.nthSeries (p ^ v) i))) :=
    Module.nontrivial_of_finrank_pos (R := 𝕜) (by rw [hrk]; exact hp0)
  haveI : IsArtinianRing (MvPowerSeries (Fin d) 𝕜 ⧸ Ideal.span (Set.range fun i =>
      MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) (F.nthSeries (p ^ v) i))) :=
    IsArtinianRing.of_finite 𝕜 _
  have hdim0 : ringKrullDim (MvPowerSeries (Fin d) 𝕜 ⧸ Ideal.span (Set.range fun i =>
      MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) (F.nthSeries (p ^ v) i))) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.1 inferInstance

  haveI : IsRegularLocalRing 𝔸 := IsRegularLocalRing.mvPowerSeries_fin 𝓞 d
  have hCM : (Module.depth 𝔸 𝔸 : WithBot ℕ∞) = ringKrullDim 𝔸 :=
    MvPowerSeries.depth_self_eq_ringKrullDim_fin_of_isDiscreteValuationRing 𝓞 d
  have hdim : ringKrullDim 𝔸 = (d + 1 : ℕ) := by
    rw [← hCM, MvPowerSeries.depth_self_fin_eq_of_isDiscreteValuationRing 𝓞 d]; rfl
  have hCp : (C (p : 𝓞) : 𝔸) ∈ IsLocalRing.maximalIdeal 𝔸 :=
    (IsLocalRing.mem_maximalIdeal _).2 fun hu => hpu (by rwa [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_C] at hu)

  have hofList : Ideal.ofList (List.ofFn (F.nthSeries (p ^ v))) = Ideal.span (Set.range (F.nthSeries (p ^ v))) :=
    congrArg Ideal.span (Set.ext fun r => List.mem_ofFn' _ r)
  have hreg : RingTheory.Sequence.IsRegular 𝔸 (List.ofFn (F.nthSeries (p ^ v)) ++ [C (p : 𝓞)]) := by
    refine IsLocalRing.isRegular_of_systemOfParameters hCM hdim _ (by simp) ?_ ?_
    · intro y hy
      rw [List.mem_append, List.mem_ofFn', List.mem_singleton] at hy
      rcases hy with ⟨i, rfl⟩ | rfl
      · exact (IsLocalRing.mem_maximalIdeal _).2 fun hu => not_isUnit_zero
          (by rwa [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_nthSeries] at hu)
      · exact hCp
    · rw [Ideal.ofList_append, Ideal.ofList_singleton, hofList]
      exact (ringKrullDim_eq_of_ringEquiv (quotSupEquiv (p : 𝓞) (F.nthSeries (p ^ v)))).trans hdim0

  have hregB : IsSMulRegular (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) (p : 𝓞) := by
    have h1 := ((RingTheory.Sequence.isWeaklyRegular_append_iff 𝔸 _ _).1 hreg.toIsWeaklyRegular).2
    rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff] at h1
    have h2 : (Ideal.ofList (List.ofFn (F.nthSeries (p ^ v))) • ⊤ : Submodule 𝔸 𝔸) =
        Ideal.span (Set.range (F.nthSeries (p ^ v))) := by
      rw [hofList, smul_eq_mul, Ideal.mul_top]
    have h3 : IsSMulRegular (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) (C (p : 𝓞) : 𝔸) :=
      ((Submodule.quotEquivOfEq _ _ h2).isSMulRegular_congr (C (p : 𝓞) : 𝔸)).1 h1
    have h4 : (algebraMap 𝓞 𝔸 (p : 𝓞)) = C (p : 𝓞) := by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]
    rw [← isSMulRegular_algebraMap_iff 𝔸, h4]
    exact h3

  let e := quotSMulTopEquiv' (p : 𝓞) (F.nthSeries (p ^ v))
  have hrkQ : Module.finrank 𝕜 (QuotSMulTop (p : 𝓞) (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v))))) =
      p ^ (v * h) := by
    rw [e.finrank_eq, hrk]
  haveI : Module.Finite 𝕜 (QuotSMulTop (p : 𝓞) (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v))))) :=
    Module.finite_of_finrank_pos (by rw [hrkQ]; exact hp0)
  have hfreeQ : Module.Free 𝕜 (QuotSMulTop (p : 𝓞) (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v))))) :=
    inferInstance
  haveI : IsScalarTower 𝓞 𝕜 (QuotSMulTop (p : 𝓞) (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v))))) :=
    IsScalarTower.of_algebraMap_smul fun r x =>
      Module.IsTorsionBy.mk_smul (Module.isTorsionBy_quotient_element_smul _ (p : 𝓞)) r x
  haveI : Module.Finite 𝓞 (QuotSMulTop (p : 𝓞) (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v))))) :=
    Module.Finite.trans 𝕜 _

  haveI : IsHausdorff (Ideal.span {(p : 𝓞)}) (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) := by
    have hle : Ideal.span {(C (p : 𝓞) : 𝔸)} ≤ Ideal.jacobson ⊥ := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
      exact hCp
    haveI : Module.Finite 𝔸 (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝔸 (Ideal.span (Set.range (F.nthSeries (p ^ v))))).toLinearMap
        (Ideal.Quotient.mkₐ_surjective 𝔸 _)
    have hiInf := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
      (M := 𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) _ hle
    haveI : IsHausdorff (Ideal.span {(C (p : 𝓞) : 𝔸)}) (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) :=
      ⟨fun x hx => by
        have hx' : x ∈ (⨅ i : ℕ, Ideal.span {(C (p : 𝓞) : 𝔸)} ^ i • ⊤ :
            Submodule 𝔸 (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v))))) :=
          (Submodule.mem_iInf _).2 fun i => SModEq.zero.1 (hx i)
        rwa [hiInf, Submodule.mem_bot] at hx'⟩
    exact IsHausdorff.of_map (I := Ideal.span {(p : 𝓞)}) (J := Ideal.span {(C (p : 𝓞) : 𝔸)})
      (le_of_eq (by rw [Ideal.map_span, Set.image_singleton, MvPowerSeries.algebraMap_apply,
        Algebra.algebraMap_self_apply]))

  have hfin : Module.Finite 𝓞 (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) := by
    have hfinq : Module.Finite 𝓞 ((𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) ⧸
        (Ideal.span {(p : 𝓞)} • ⊤ : Submodule 𝓞 (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))))) :=
      Module.Finite.equiv (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul (p : 𝓞) ⊤).symm)
    exact Module.Finite.of_isAdicComplete_of_isHausdorff_of_quotient (Ideal.span {(p : 𝓞)}) _ hfinq

  haveI := hfin
  have hfree : Module.Free 𝓞 (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) :=
    Module.free_of_quotSMulTop_free (p : 𝓞) hpm hregB hfreeQ
  have hrank : Module.finrank 𝓞 (𝔸 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) = p ^ (v * h) := by
    rw [← Module.finrank_quotSMulTop_eq (p : 𝓞) hpm hregB hfreeQ, hrkQ]
  exact ⟨hfin, hfree, hrank⟩

end Main

end LevelFree

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) (h v : ℕ)
    (hrk : Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((F.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries (p ^ v)))) =
      p ^ (v * h)) :
    Module.Finite 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) ∧
    Module.Free 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) ∧
    Module.finrank 𝓞 (MvPowerSeries (Fin d) 𝓞 ⧸ Ideal.span (Set.range (F.nthSeries (p ^ v)))) =
      p ^ (v * h) :=
  LevelFree.main p hp F h v hrk

end S_MvFormalGroup_finite_free_finrank_quotient_span_nthSeries_of_finrank_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_finite_free_finrank_quotient_span_nthSeries_of_finrank_eq_pow (solution)
