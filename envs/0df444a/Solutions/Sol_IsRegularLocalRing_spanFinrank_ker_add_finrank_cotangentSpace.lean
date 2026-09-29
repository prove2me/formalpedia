-- Prove2me | solution 1 for IsRegularLocalRing.spanFinrank_ker_add_finrank_cotangentSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/009e4315-8452-5e15-8a5e-7800dfcbd54f

import Mathlib
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_spanFinrank_ker_add_finrank_cotangentSpace

universe u v

open IsLocalRing

namespace RegularImmersion

open Submodule

theorem mem_maximalIdeal_of_apply_mem {P : Type u} [CommRing P] [IsLocalRing P]
    {S : Type v} [CommRing S] [IsLocalRing S] (f : P →+* S) {y : P}
    (hy : f y ∈ maximalIdeal S) : y ∈ maximalIdeal P := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
  exact fun hu => hy (hu.map f)

theorem spanFinrank_maximalIdeal_le_of_surjective {P : Type u} [CommRing P] [IsLocalRing P]
    [IsNoetherianRing P] {S : Type v} [CommRing S] [IsLocalRing S] (f : P →+* S)
    (hf : Function.Surjective f) :
    (maximalIdeal S).spanFinrank ≤ (maximalIdeal P).spanFinrank := by
  rw [← map_maximalIdeal_of_surjective f hf]
  exact Ideal.spanFinrank_map_le_of_fg f (IsNoetherian.noetherian _)

theorem spanFinrank_maximalIdeal_le {P : Type u} [CommRing P] [IsLocalRing P]
    [IsNoetherianRing P] {S : Type v} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (f : P →+* S) (hf : Function.Surjective f) :
    (maximalIdeal P).spanFinrank ≤
      (RingHom.ker f).spanFinrank + (maximalIdeal S).spanFinrank := by
  classical
  obtain ⟨G, hGcard, hGspan⟩ :=
    FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (RingHom.ker f))
  obtain ⟨T, hTcard, hTspan⟩ :=
    FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal S))
  have hsurj := hf
  choose y hy using hsurj
  have hG : Ideal.span (G : Set P) = RingHom.ker f := hGspan
  have hT : Ideal.span (T : Set S) = maximalIdeal S := hTspan
  have himage : f '' (y '' (T : Set S)) = (T : Set S) := by
    ext s
    simp only [Set.mem_image, exists_exists_and_eq_and, hy, exists_eq_right]
  have hspan : Ideal.span ((G : Set P) ∪ y '' (T : Set S)) = maximalIdeal P := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro z (hz | ⟨t, ht, rfl⟩)
      · exact le_maximalIdeal (RingHom.ker_ne_top f) (hG ▸ Ideal.subset_span hz)
      · exact mem_maximalIdeal_of_apply_mem f ((hy t).symm ▸ hT ▸ Ideal.subset_span ht)
    · intro z hz
      have hfz : f z ∈ (Ideal.span (y '' (T : Set S))).map f := by
        rw [Ideal.map_span, himage, hT, ← map_maximalIdeal_of_surjective f hf]
        exact Ideal.mem_map_of_mem f hz
      obtain ⟨w, hw, hwz⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hfz
      have hzw : z - w ∈ Ideal.span (G : Set P) := by
        rw [hG, RingHom.mem_ker, map_sub, hwz, sub_self]
      rw [Ideal.span_union]
      simpa using Submodule.add_mem_sup hzw hw
  rw [← hspan, ← hGcard, ← hTcard]
  calc (Ideal.span ((G : Set P) ∪ y '' (T : Set S))).spanFinrank
      ≤ ((G : Set P) ∪ y '' (T : Set S)).ncard :=
        spanFinrank_span_le_ncard_of_finite ((G.finite_toSet).union (T.finite_toSet.image y))
    _ ≤ (G : Set P).ncard + (y '' (T : Set S)).ncard := Set.ncard_union_le _ _
    _ ≤ G.card + T.card := by
        rw [Set.ncard_coe_finset]
        gcongr
        exact (Set.ncard_image_le T.finite_toSet).trans (Set.ncard_coe_finset T).le

theorem ker_eq_bot_of_ker_le_sq {P : Type u} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    {S : Type v} [CommRing S] [IsRegularLocalRing S] (f : P →+* S)
    (hf : Function.Surjective f) (hker : RingHom.ker f ≤ maximalIdeal P ^ 2) :
    RingHom.ker f = ⊥ := by
  classical

  have hA : (maximalIdeal P).spanFinrank ≤ (maximalIdeal S).spanFinrank := by
    obtain ⟨T, hTcard, hTspan⟩ :=
      FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal S))
    have hsurj := hf
    choose y hy using hsurj
    have hT : Ideal.span (T : Set S) = maximalIdeal S := hTspan
    have himage : f '' (y '' (T : Set S)) = (T : Set S) := by
      ext s
      simp only [Set.mem_image, exists_exists_and_eq_and, hy, exists_eq_right]
    set N : Ideal P := Ideal.span (y '' (T : Set S)) with hN
    have hNle : N ≤ maximalIdeal P := by
      rw [hN, Ideal.span_le]
      rintro z ⟨t, ht, rfl⟩
      exact mem_maximalIdeal_of_apply_mem f ((hy t).symm ▸ hT ▸ Ideal.subset_span ht)
    have hle : maximalIdeal P ≤ N ⊔ maximalIdeal P • maximalIdeal P := by
      intro z hz
      have hfz : f z ∈ N.map f := by
        rw [hN, Ideal.map_span, himage, hT, ← map_maximalIdeal_of_surjective f hf]
        exact Ideal.mem_map_of_mem f hz
      obtain ⟨w, hw, hwz⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hfz
      have hzw : z - w ∈ maximalIdeal P • maximalIdeal P := by
        rw [smul_eq_mul, ← pow_two]
        exact hker (by rw [RingHom.mem_ker, map_sub, hwz, sub_self])
      simpa using Submodule.add_mem_sup hw hzw
    have hmN : maximalIdeal P = N :=
      le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle) hNle
    rw [hmN, hN, ← hTcard]
    exact (spanFinrank_span_le_ncard_of_finite (T.finite_toSet.image y)).trans
      ((Set.ncard_image_le T.finite_toSet).trans (Set.ncard_coe_finset T).le)

  have hPS : ringKrullDim S ≤ ringKrullDim P := ringKrullDim_le_of_surjective f hf
  haveI : IsRegularLocalRing P := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le P <|
    calc ((maximalIdeal P).spanFinrank : WithBot ℕ∞) ≤ (maximalIdeal S).spanFinrank := by
          exact_mod_cast hA
      _ = ringKrullDim S := IsRegularLocalRing.spanFinrank_maximalIdeal
      _ ≤ ringKrullDim P := hPS

  haveI : IsDomain P := IsRegularLocalRing.isDomain P

  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxm : x ∈ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top f) hx
  have hlift : ∀ a : P, a ∈ Ideal.span {x} → f a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, RingHom.mem_ker.mp hx, mul_zero]
  have hSq : ringKrullDim S ≤ ringKrullDim (P ⧸ Ideal.span {x}) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.lift_surjective_of_surjective _ hlift hf)
  have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hx0) hxm
  haveI := RegularQuotientEngine.isLocalRing_quotient_span_singleton P hxm
  obtain ⟨d, hd⟩ := RegularQuotientEngine.exists_ringKrullDim_eq_natCast (P ⧸ Ideal.span {x})
  have hS : ringKrullDim S = ((maximalIdeal S).spanFinrank : WithBot ℕ∞) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  have hP : ringKrullDim P = ((maximalIdeal P).spanFinrank : WithBot ℕ∞) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  rw [hd, hP] at hdrop
  rw [hd, hS] at hSq
  have h₁ : d + 1 = (maximalIdeal P).spanFinrank := by exact_mod_cast hdrop
  have h₂ : (maximalIdeal S).spanFinrank ≤ d := by exact_mod_cast hSq
  omega

theorem spanFinrank_ker_le_succ {P : Type u} [CommRing P] [IsNoetherianRing P]
    {S : Type v} [CommRing S] (f : P →+* S) {x : P}
    (hlift : ∀ a : P, a ∈ Ideal.span {x} → f a = 0) :
    (RingHom.ker f).spanFinrank ≤
      (RingHom.ker (Ideal.Quotient.lift (Ideal.span {x}) f hlift)).spanFinrank + 1 := by
  classical
  set f₁ := Ideal.Quotient.lift (Ideal.span {x}) f hlift with hf₁
  obtain ⟨T, hTcard, hTspan⟩ :=
    FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (RingHom.ker f₁))
  have hT : Ideal.span (T : Set (P ⧸ Ideal.span {x})) = RingHom.ker f₁ := hTspan
  choose y hy using Ideal.Quotient.mk_surjective (I := Ideal.span {x})
  have himage : Ideal.Quotient.mk (Ideal.span {x}) '' (y '' (T : Set _)) = (T : Set _) := by
    ext s
    simp only [Set.mem_image, exists_exists_and_eq_and, hy, exists_eq_right]
  have hx : x ∈ RingHom.ker f := by
    rw [RingHom.mem_ker]
    exact hlift x (Ideal.mem_span_singleton_self x)
  have hspan : RingHom.ker f = Ideal.span (insert x (y '' (T : Set _))) := by
    apply le_antisymm
    · intro z hz
      have hz₁ : Ideal.Quotient.mk (Ideal.span {x}) z ∈ (Ideal.span (y '' (T : Set _))).map
          (Ideal.Quotient.mk (Ideal.span {x})) := by
        rw [Ideal.map_span, himage, hT, RingHom.mem_ker, hf₁, Ideal.Quotient.lift_mk]
        exact RingHom.mem_ker.mp hz
      obtain ⟨w, hw, hwz⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hz₁
      have hzw : z - w ∈ Ideal.span {x} := (Ideal.Quotient.eq).mp hwz.symm
      rw [Set.insert_eq, Ideal.span_union]
      simpa using Submodule.add_mem_sup hzw hw
    · rw [Ideal.span_le]
      rintro z (rfl | ⟨t, ht, rfl⟩)
      · exact hx
      · have ht₁ : f₁ t = 0 := RingHom.mem_ker.mp (hT ▸ Ideal.subset_span ht)
        rw [SetLike.mem_coe, RingHom.mem_ker, ← Ideal.Quotient.lift_mk (Ideal.span {x}) f hlift,
          ← hf₁, hy t, ht₁]
  rw [hspan, ← hTcard]
  calc (Ideal.span (insert x (y '' (T : Set _)))).spanFinrank
      ≤ (insert x (y '' (T : Set _))).ncard :=
        spanFinrank_span_le_ncard_of_finite ((T.finite_toSet.image y).insert x)
    _ ≤ (y '' (T : Set _)).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ T.card + 1 := by
        gcongr
        exact (Set.ncard_image_le T.finite_toSet).trans (Set.ncard_coe_finset T).le

theorem spanFinrank_ker_add_le {P : Type u} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    {S : Type v} [CommRing S] [IsRegularLocalRing S] (f : P →+* S)
    (hf : Function.Surjective f) :
    (RingHom.ker f).spanFinrank + (maximalIdeal S).spanFinrank ≤
      (maximalIdeal P).spanFinrank := by
  suffices key : ∀ (n : ℕ) (P : Type u) [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
      (f : P →+* S), Function.Surjective f → (maximalIdeal P).spanFinrank ≤ n →
        (RingHom.ker f).spanFinrank + (maximalIdeal S).spanFinrank ≤
          (maximalIdeal P).spanFinrank from key _ P f hf le_rfl
  intro n
  induction n with
  | zero =>
    intro P _ _ _ f hf hn
    by_cases hker : RingHom.ker f ≤ maximalIdeal P ^ 2
    · rw [ker_eq_bot_of_ker_le_sq f hf hker, Submodule.spanFinrank_bot, zero_add]
      exact spanFinrank_maximalIdeal_le_of_surjective f hf
    · obtain ⟨x, hxk, hx2⟩ := SetLike.not_le_iff_exists.mp hker
      have hxm : x ∈ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top f) hxk
      have := RegularQuotientEngine.one_le_spanFinrank_maximalIdeal_of_notMem_sq P hxm hx2
      omega
  | succ n ih =>
    intro P _ _ _ f hf hn
    by_cases hker : RingHom.ker f ≤ maximalIdeal P ^ 2
    · rw [ker_eq_bot_of_ker_le_sq f hf hker, Submodule.spanFinrank_bot, zero_add]
      exact spanFinrank_maximalIdeal_le_of_surjective f hf
    · obtain ⟨x, hxk, hx2⟩ := SetLike.not_le_iff_exists.mp hker
      have hxm : x ∈ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top f) hxk
      have h₁ := RegularQuotientEngine.one_le_spanFinrank_maximalIdeal_of_notMem_sq P hxm hx2
      haveI := RegularQuotientEngine.isLocalRing_quotient_span_singleton P hxm
      have h₂ := RegularQuotientEngine.spanFinrank_maximalIdeal_quotient_le_sub_one P hxm hx2
      have hlift : ∀ a : P, a ∈ Ideal.span {x} → f a = 0 := by
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, RingHom.mem_ker.mp hxk, mul_zero]
      have h₃ := ih (P ⧸ Ideal.span {x}) (Ideal.Quotient.lift (Ideal.span {x}) f hlift)
        (Ideal.Quotient.lift_surjective_of_surjective _ hlift hf) (by omega)
      have h₄ := spanFinrank_ker_le_succ f hlift
      omega

end RegularImmersion

open RegularImmersion in
theorem solution {P : Type u} {S : Type v}
    [CommRing P] [IsLocalRing P] [IsNoetherianRing P] [CommRing S] [IsRegularLocalRing S]
    (f : P →+* S) (hf : Function.Surjective f) :
    (RingHom.ker f).spanFinrank + Module.finrank (ResidueField S) (CotangentSpace S) =
      Module.finrank (ResidueField P) (CotangentSpace P) := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace S,
    ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace P]
  exact le_antisymm (spanFinrank_ker_add_le f hf) (spanFinrank_maximalIdeal_le f hf)

end S_IsRegularLocalRing_spanFinrank_ker_add_finrank_cotangentSpace
end P2MW
export P2MW.S_IsRegularLocalRing_spanFinrank_ker_add_finrank_cotangentSpace (solution)
