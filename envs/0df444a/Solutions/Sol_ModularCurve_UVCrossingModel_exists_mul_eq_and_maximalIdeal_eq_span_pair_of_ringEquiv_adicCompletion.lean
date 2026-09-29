-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_mul_eq_and_maximalIdeal_eq_span_pair_of_ringEquiv_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d4e65fc6-eafd-5f25-838c-35dcd696549f

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isRegularLocalRing
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_eq_two
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_ModularCurve_UVCrossingModel_isPrime_span_U
import Theorems.Thm_ModularCurve_UVCrossingModel_isPrime_span_V
import Theorems.Thm_ModularCurve_UVCrossingModel_U_notMem_span_V
import Theorems.Thm_ModularCurve_UVCrossingModel_V_notMem_span_U
import Theorems.Thm_ModularCurve_UVCrossingModel_minimalPrimes_span_U_mul_V
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
import Theorems.Thm_IsLocalRing_comap_map_adicCompletion_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_mul_eq_and_maximalIdeal_eq_span_pair_of_ringEquiv_adicCompletion

set_option autoImplicit false

universe u

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace DescentProof

section completion

variable {O : Type u} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]

theorem isUnit_of_isUnit_algebraMap (x : O)
    (hx : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) x)) : IsUnit x := by
  rw [← Ideal.span_singleton_eq_top]
  have h := IsLocalRing.comap_map_adicCompletion_eq (Ideal.span {x})
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top.mpr hx, Ideal.comap_top] at h
  exact h.symm

theorem algebraMap_injective :
    Function.Injective (algebraMap O (AdicCompletion (maximalIdeal O) O)) := by
  intro a b h
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    RingHom.id_apply] at h
  exact AdicCompletion.of_injective (maximalIdeal O) O h

theorem comap_map_eq {R : Type u} [CommRing R] (e : AdicCompletion (maximalIdeal O) O ≃+* R) (I : Ideal O) :
    (I.map (e.toRingHom.comp (algebraMap O _))).comap (e.toRingHom.comp (algebraMap O _)) = I := by
  rw [← Ideal.map_map, ← Ideal.comap_comap,
    Ideal.comap_map_of_bijective e.toRingHom (show Function.Bijective e.toRingHom from e.bijective)]
  exact IsLocalRing.comap_map_adicCompletion_eq I

theorem exists_sub_mem_map_sq (y : AdicCompletion (maximalIdeal O) O) :
    ∃ x : O, algebraMap O _ x - y ∈ (maximalIdeal O ^ 2).map (algebraMap O (AdicCompletion (maximalIdeal O) O)) := by
  classical
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal O) O 2 y)
  refine ⟨x, ?_⟩
  have hker : algebraMap O _ x - y ∈ LinearMap.ker (AdicCompletion.eval (maximalIdeal O) O 2) := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, AdicCompletion.eval_of, ← hx]
    rfl
  have hfg : (maximalIdeal O).FG := IsNoetherian.noetherian _
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval hfg, Ideal.smul_top_eq_map] at hker
  exact hker

end completion

section model

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  {ϖ : A} (hϖ : maximalIdeal A = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)

include hϖ in

theorem isDomain_quotient_span : IsDomain (A ⧸ Ideal.span {ϖ}) := by
  rw [Ideal.Quotient.isDomain_iff_prime, ← hϖ]
  infer_instance

theorem span_pair_unit_mul {R : Type u} [CommRing R] (x y c d : R) (hc : IsUnit c) (hd : IsUnit d) :
    Ideal.span {c * x, d * y} = Ideal.span {x, y} := by
  have hx : x ∈ Ideal.span ({x, y} : Set R) := Ideal.subset_span (Set.mem_insert _ _)
  have hy : y ∈ Ideal.span ({x, y} : Set R) := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hcx : c * x ∈ Ideal.span ({c * x, d * y} : Set R) := Ideal.subset_span (Set.mem_insert _ _)
  have hdy : d * y ∈ Ideal.span ({c * x, d * y} : Set R) := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Ideal.mul_mem_left _ _ hx, Ideal.mul_mem_left _ _ hy⟩
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    obtain ⟨c', hc'⟩ := hc.exists_left_inv
    obtain ⟨d', hd'⟩ := hd.exists_left_inv
    constructor
    · have h := Ideal.mul_mem_left _ c' hcx
      rwa [← mul_assoc, hc', one_mul] at h
    · have h := Ideal.mul_mem_left _ d' hdy
      rwa [← mul_assoc, hd', one_mul] at h

end model

end DescentProof

open DescentProof in
set_option maxHeartbeats 6400000 in
theorem solution
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (e : AdicCompletion (IsLocalRing.maximalIdeal O) O ≃+* ModularCurve.UVCrossingModel A ϖ)
    (t : O) (ht : e (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) t) = ModularCurve.UVCrossingModel.const ϖ ϖ)
    (hmany : ¬ ((Ideal.span {t} : Ideal O).minimalPrimes).Subsingleton) :
    ∃ u v : O, u * v = t ∧ IsLocalRing.maximalIdeal O = Ideal.span {u, v} := by
  classical

  haveI hreg : IsRegularLocalRing (UVCrossingModel A ϖ) := UVCrossingModel.isRegularLocalRing hϖ hϖ0
  haveI : IsDomain (UVCrossingModel A ϖ) := IsRegularLocalRing.isDomain _
  haveI : IsDomain (A ⧸ Ideal.span {ϖ}) := isDomain_quotient_span hϖ
  have hmR : maximalIdeal (UVCrossingModel A ϖ) = Ideal.span {U ϖ, V ϖ} :=
    UVCrossingModel.maximalIdeal_eq_span_pair hϖ
  have hUm : U ϖ ∈ maximalIdeal (UVCrossingModel A ϖ) := hmR ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hVm : V ϖ ∈ maximalIdeal (UVCrossingModel A ϖ) := hmR ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hU0 : U ϖ ≠ 0 := fun h => UVCrossingModel.U_notMem_span_V ϖ (h ▸ zero_mem _)
  have hV0 : V ϖ ≠ 0 := fun h => UVCrossingModel.V_notMem_span_U ϖ (h ▸ zero_mem _)
  have hUV0 : U ϖ * V ϖ ≠ 0 := mul_ne_zero hU0 hV0

  set f : O →+* UVCrossingModel A ϖ := e.toRingHom.comp (algebraMap O (AdicCompletion (maximalIdeal O) O)) with hf
  have hfapp : ∀ x, f x = e (algebraMap O (AdicCompletion (maximalIdeal O) O) x) := fun x => rfl
  have hft : f t = U ϖ * V ϖ := by rw [hfapp, ht, UVCrossingModel.U_mul_V]
  have hfinj : Function.Injective f := e.injective.comp algebraMap_injective
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hUV0 (by rw [← hft, map_zero])
  have hcm : ∀ I : Ideal O, (I.map f).comap f = I := fun I => comap_map_eq e I
  have hunit : ∀ x : O, IsUnit (f x) → IsUnit x := by
    intro x hx
    apply isUnit_of_isUnit_algebraMap x
    have h := hx.map e.symm
    rwa [hfapp, RingEquiv.symm_apply_apply] at h
  have hcomap : (maximalIdeal (UVCrossingModel A ϖ)).comap f = maximalIdeal O := by
    apply le_antisymm
    · intro x hx
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp hx))) (hu.map f)
    · intro x hx
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hx)) (hunit x hu)

  have transfer : ∀ u v : O, Ideal.span {f u, f v} = maximalIdeal (UVCrossingModel A ϖ) →
      maximalIdeal O = Ideal.span {u, v} := by
    intro u v huv
    have h1 : (Ideal.span {u, v}).map f = Ideal.span {f u, f v} := by rw [Ideal.map_span, Set.image_pair]
    rw [← hcomap, ← huv, ← h1, hcm]
  haveI : IsDomain O := Function.Injective.isDomain f hfinj

  have hmapsq : ((maximalIdeal O ^ 2).map (algebraMap O (AdicCompletion (maximalIdeal O) O))).map e.toRingHom ≤
      maximalIdeal (UVCrossingModel A ϖ) ^ 2 := by
    rw [Ideal.map_map, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hcomap.ge) 2
  obtain ⟨u₀, hu₀⟩ := exists_sub_mem_map_sq (O := O) (e.symm (U ϖ))
  obtain ⟨v₀, hv₀⟩ := exists_sub_mem_map_sq (O := O) (e.symm (V ϖ))
  have hU : f u₀ - U ϖ ∈ maximalIdeal (UVCrossingModel A ϖ) ^ 2 := by
    have h1 : f u₀ - U ϖ = e (algebraMap O _ u₀ - e.symm (U ϖ)) := by
      rw [map_sub, RingEquiv.apply_symm_apply, hfapp]
    rw [h1]
    exact hmapsq (Ideal.mem_map_of_mem e.toRingHom hu₀)
  have hV : f v₀ - V ϖ ∈ maximalIdeal (UVCrossingModel A ϖ) ^ 2 := by
    have h1 : f v₀ - V ϖ = e (algebraMap O _ v₀ - e.symm (V ϖ)) := by
      rw [map_sub, RingEquiv.apply_symm_apply, hfapp]
    rw [h1]
    exact hmapsq (Ideal.mem_map_of_mem e.toRingHom hv₀)
  have hsq_le : maximalIdeal (UVCrossingModel A ϖ) ^ 2 ≤ maximalIdeal (UVCrossingModel A ϖ) :=
    Ideal.pow_le_self two_ne_zero
  have hgen₀ : Ideal.span {f u₀, f v₀} = maximalIdeal (UVCrossingModel A ϖ) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · have key : U ϖ + (f u₀ - U ϖ) ∈ maximalIdeal (UVCrossingModel A ϖ) :=
          add_mem hUm (hsq_le hU)
        rwa [add_sub_cancel] at key
      · have key : V ϖ + (f v₀ - V ϖ) ∈ maximalIdeal (UVCrossingModel A ϖ) :=
          add_mem hVm (hsq_le hV)
        rwa [add_sub_cancel] at key
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (IsLocalRing.maximalIdeal_le_jacobson _) ?_
      refine hmR.le.trans ?_
      rw [Ideal.span_le]
      have hsq : maximalIdeal (UVCrossingModel A ϖ) ^ 2 ≤
          Ideal.span {f u₀, f v₀} ⊔ maximalIdeal (UVCrossingModel A ϖ) • maximalIdeal (UVCrossingModel A ϖ) := by
        rw [Ideal.smul_eq_mul, ← pow_two]
        exact le_sup_right
      rintro z (rfl | rfl)
      · have key : f u₀ - (f u₀ - U ϖ) ∈
            Ideal.span {f u₀, f v₀} ⊔ maximalIdeal (UVCrossingModel A ϖ) • maximalIdeal (UVCrossingModel A ϖ) :=
          sub_mem (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))) (hsq hU)
        rwa [sub_sub_cancel] at key
      · have key : f v₀ - (f v₀ - V ϖ) ∈
            Ideal.span {f u₀, f v₀} ⊔ maximalIdeal (UVCrossingModel A ϖ) • maximalIdeal (UVCrossingModel A ϖ) :=
          sub_mem (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))) (hsq hV)
        rwa [sub_sub_cancel] at key
  have h𝔪₀ : maximalIdeal O = Ideal.span {u₀, v₀} := transfer u₀ v₀ hgen₀
  have hspan : (maximalIdeal O).spanFinrank ≤ 2 := by
    rw [h𝔪₀]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

  obtain ⟨𝔮₁, h𝔮₁, 𝔮₂, h𝔮₂, hne⟩ := Set.not_subsingleton_iff.mp hmany
  have hqne : ∃ 𝔮 ∈ (Ideal.span {t} : Ideal O).minimalPrimes, 𝔮 ≠ maximalIdeal O := by
    by_cases h : 𝔮₁ = maximalIdeal O
    · exact ⟨𝔮₂, h𝔮₂, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨𝔮₁, h𝔮₁, h⟩
  obtain ⟨𝔮, h𝔮, h𝔮ne⟩ := hqne
  have hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim O := by
    haveI := h𝔮.1.1
    have htq : t ∈ 𝔮 := h𝔮.1.2 (Ideal.subset_span rfl)
    have h𝔮bot : 𝔮 ≠ ⊥ := fun h => ht0 (by simpa [h] using htq)
    have hbot : (⊥ : Ideal O) < 𝔮 := bot_lt_iff_ne_bot.mpr h𝔮bot
    have hlt : 𝔮 < maximalIdeal O := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal h𝔮.1.1.ne_top) h𝔮ne
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [Ideal.height_bot, zero_add] at h1
    have h3 : (2 : ℕ∞) ≤ (maximalIdeal O).height :=
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ 𝔮.height + 1 := add_le_add h1 le_rfl
        _ ≤ _ := h2
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h4 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (maximalIdeal O).height := WithBot.coe_le_coe.mpr h3
    rwa [WithBot.coe_ofNat] at h4
  haveI hregO : IsRegularLocalRing O := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le O ?_
    calc ((maximalIdeal O).spanFinrank : WithBot ℕ∞) ≤ 2 := by exact_mod_cast hspan
      _ ≤ ringKrullDim O := hdim2
  have hdimle : ringKrullDim O ≤ 2 :=
    (ringKrullDim_le_spanFinrank_maximalIdeal O).trans (by exact_mod_cast hspan)
  haveI : UniqueFactorizationMonoid O := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two O hdimle

  set P_U : Ideal O := (Ideal.span {U ϖ}).comap f with hPU_def
  set P_V : Ideal O := (Ideal.span {V ϖ}).comap f with hPV_def
  have hspan_t : (Ideal.span {U ϖ * V ϖ}).comap f = Ideal.span {t} := by
    rw [← hft, show Ideal.span {f t} = (Ideal.span {t}).map f by rw [Ideal.map_span, Set.image_singleton], hcm]
  have hmin : ∀ 𝔭 ∈ (Ideal.span {t} : Ideal O).minimalPrimes, 𝔭 = P_U ∨ 𝔭 = P_V := by
    intro 𝔭 h𝔭
    rw [← hspan_t] at h𝔭
    obtain ⟨𝔔, h𝔔, rfl⟩ := Ideal.exists_minimalPrimes_comap_eq f 𝔭 h𝔭
    rw [UVCrossingModel.minimalPrimes_span_U_mul_V ϖ] at h𝔔
    rcases h𝔔 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hPUPV : P_U ∈ (Ideal.span {t} : Ideal O).minimalPrimes ∧ P_V ∈ (Ideal.span {t} : Ideal O).minimalPrimes ∧
      P_U ≠ P_V := by
    rcases hmin 𝔮₁ h𝔮₁ with h1 | h1 <;> rcases hmin 𝔮₂ h𝔮₂ with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact ⟨h1 ▸ h𝔮₁, h2 ▸ h𝔮₂, fun h' => hne (h1.trans (h'.trans h2.symm))⟩
    · exact ⟨h2 ▸ h𝔮₂, h1 ▸ h𝔮₁, fun h' => hne (h1.trans (h'.symm.trans h2.symm))⟩
    · exact absurd (h1.trans h2.symm) hne
  obtain ⟨hPUmin, hPVmin, hPne⟩ := hPUPV
  haveI hPUp : P_U.IsPrime := hPUmin.1.1
  haveI hPVp : P_V.IsPrime := hPVmin.1.1
  have htPU : t ∈ P_U := hPUmin.1.2 (Ideal.subset_span rfl)
  have htPV : t ∈ P_V := hPVmin.1.2 (Ideal.subset_span rfl)
  have hheight : ∀ P : Ideal O, P ∈ (Ideal.span {t} : Ideal O).minimalPrimes → t ∈ P → P.height = 1 := by
    intro P hP htP
    haveI := hP.1.1
    apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {t}) P hP)
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro hbot
    exact ht0 (by simpa [hbot] using htP)
  haveI := IsRegularLocalRing.isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two hdimle P_U hPUp
    (hheight P_U hPUmin htPU)
  haveI := IsRegularLocalRing.isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two hdimle P_V hPVp
    (hheight P_V hPVmin htPV)
  obtain ⟨u₁, hu₁⟩ := Submodule.IsPrincipal.principal P_U
  obtain ⟨v₁, hv₁⟩ := Submodule.IsPrincipal.principal P_V

  have htPU' : t ∈ Ideal.span {u₁} := by rw [hu₁] at htPU; exact htPU
  have htPV' : t ∈ Ideal.span {v₁} := by rw [hv₁] at htPV; exact htPV
  have hv₁0 : v₁ ≠ 0 := by
    rintro rfl
    apply ht0
    simpa using htPV'
  have hv₁prime : Prime v₁ := by
    rw [← Ideal.span_singleton_prime hv₁0, show Ideal.span {v₁} = P_V from hv₁.symm]
    exact hPVp
  obtain ⟨a, ha⟩ : ∃ a, a * u₁ = t := Ideal.mem_span_singleton'.mp htPU'
  have hva : v₁ ∣ a := by
    rcases hv₁prime.dvd_or_dvd (show v₁ ∣ a * u₁ from ha ▸ Ideal.mem_span_singleton.mp htPV') with h | h
    · exact h
    · exfalso
      apply hPne
      have hle : P_U ≤ P_V := by
        rw [hu₁, hv₁]
        exact (Ideal.span_singleton_le_span_singleton).mpr h
      exact le_antisymm hle (hPVmin.2 ⟨hPUp, hPUmin.1.2⟩ hle)
  obtain ⟨w, hw⟩ := hva
  have htw : t = w * u₁ * v₁ := by rw [← ha, hw]; ring

  obtain ⟨r, hr⟩ : ∃ r, r * U ϖ = f u₁ :=
    Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp (show u₁ ∈ P_U by rw [hu₁]; exact Ideal.mem_span_singleton_self u₁))
  obtain ⟨s, hs⟩ : ∃ s, s * V ϖ = f v₁ :=
    Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp (show v₁ ∈ P_V by rw [hv₁]; exact Ideal.mem_span_singleton_self v₁))
  have hprod : f w * (r * s) = 1 := by
    have h1 : (f w * (r * s) - 1) * (U ϖ * V ϖ) = 0 := by
      have := hft
      rw [htw, map_mul, map_mul, ← hr, ← hs] at this
      linear_combination this
    rcases mul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hUV0
  have hwu : IsUnit w := hunit w (isUnit_iff_exists_inv.mpr ⟨_, hprod⟩)
  have hru : IsUnit r := isUnit_iff_exists_inv.mpr ⟨f w * s, by rw [← hprod]; ring⟩
  have hsu : IsUnit s := isUnit_iff_exists_inv.mpr ⟨f w * r, by rw [← hprod]; ring⟩

  refine ⟨w * u₁, v₁, by rw [htw], transfer (w * u₁) v₁ ?_⟩
  have h1 : f (w * u₁) = (f w * r) * U ϖ := by rw [map_mul, ← hr]; ring
  have h2 : f v₁ = s * V ϖ := hs.symm
  rw [h1, h2, span_pair_unit_mul (U ϖ) (V ϖ) (f w * r) s ((hwu.map f).mul hru) hsu, hmR]

end S_ModularCurve_UVCrossingModel_exists_mul_eq_and_maximalIdeal_eq_span_pair_of_ringEquiv_adicCompletion
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_mul_eq_and_maximalIdeal_eq_span_pair_of_ringEquiv_adicCompletion (solution)
