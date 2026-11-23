-- Prove2me | solution 1 for GlobalTheory.flat_coker_of_injective_mod_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:51.191183+00:00
-- url     : https://prove2.me/submissions/a6d8a742-87c6-4185-b7e0-7e378a0a3258

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfInjectiveModMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace GlobalTheory
open CategoryTheory CategoryTheory.Limits TensorProduct in
private theorem exists_sum_smul_of_mem_span_range_smul' {R N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] {l : ℕ} (f : Fin l → R) (P : Submodule R N) {z : N}
    (hz : z ∈ Submodule.span R (Set.range f) • P) :
    ∃ k : Fin l → N, (∀ i, k i ∈ P) ∧ z = ∑ i, f i • k i := by
  refine Submodule.smul_induction_on
    (p := fun z => ∃ k : Fin l → N, (∀ i, k i ∈ P) ∧ z = ∑ i, f i • k i) hz
    (fun r hr y hy => ?_) (fun x y hx hy => ?_)
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hr
    refine ⟨fun i => c i • y, fun i => P.smul_mem _ hy, ?_⟩
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, smul_smul, mul_comm]
  · obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨k', hk', rfl⟩ := hy
    exact ⟨k + k', fun i => P.add_mem (hk i) (hk' i), by
      simp [smul_add, Finset.sum_add_distrib]⟩
open CategoryTheory CategoryTheory.Limits TensorProduct in
private theorem flat_quotient_of_mem_ideal_smul_imp_mem_map_smul {V A N : Type*} [CommRing V] [CommRing A]
    [Algebra V A] [AddCommGroup N] [Module A N] [Module V N] [IsScalarTower V A N]
    [Module.Flat V N] (K : Submodule A N)
    (hK : ∀ I : Ideal V, ∀ z ∈ K, z ∈ I • (⊤ : Submodule V N) → z ∈ I.map (algebraMap V A) • K) :
    Module.Flat V (N ⧸ K) := by
  rw [Module.Flat.iff_forall_isTrivialRelation]
  intro l f x hsum
  choose n hn using fun i => Submodule.Quotient.mk_surjective K (x i)
  have hzK : ∑ i, f i • n i ∈ K := by
    have h1 : (K.mkQ.restrictScalars V) (∑ i, f i • n i) = 0 := by
      rw [map_sum, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, LinearMap.restrictScalars_apply, Submodule.mkQ_apply, hn]
    exact (Submodule.Quotient.mk_eq_zero K).1 h1
  have hzI : ∑ i, f i • n i ∈ Ideal.span (Set.range f) • (⊤ : Submodule V N) :=
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) Submodule.mem_top
  have h2 := hK _ _ hzK hzI
  rw [Ideal.map_span, ← Set.range_comp] at h2
  obtain ⟨k, hk, hks⟩ := exists_sum_smul_of_mem_span_range_smul' _ K h2
  have hrel : ∑ i, f i • (n i - k i) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, hks, Function.comp_apply, algebraMap_smul,
      sub_self]
  obtain ⟨p, a, y, hxy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨p, a, fun j => Submodule.Quotient.mk (y j), fun i => ?_, ha⟩
  have h3 : Submodule.Quotient.mk (p := K) (n i - k i) = Submodule.Quotient.mk (n i) := by
    rw [Submodule.Quotient.eq]
    simpa using hk i
  have h5 := hxy i
  simp only at h5
  rw [← hn i, ← h3, h5]
  exact (map_sum (K.mkQ.restrictScalars V) (fun j => a i j • y j) Finset.univ).trans
    (Finset.sum_congr rfl fun j _ => map_smul _ _ _)
open CategoryTheory CategoryTheory.Limits TensorProduct in
private theorem smul_mem_ideal_smul_of_mem_map {V A N : Type*} [CommRing V] [CommRing A]
    [Algebra V A] [AddCommGroup N] [Module A N] [Module V N] [IsScalarTower V A N] (I : Ideal V)
    {r : A} (hr : r ∈ I.map (algebraMap V A)) (y : N) : r • y ∈ I • (⊤ : Submodule V N) := by
  have hr' : r ∈ Submodule.span A (algebraMap V A '' I) := hr
  refine Submodule.span_induction
    (p := fun x _ => ∀ y : N, x • y ∈ I • (⊤ : Submodule V N))
    (fun x hx y => ?_) (fun y => by simp) (fun x x' _ _ hx hx' y => ?_)
    (fun s x _ hx y => ?_) hr' y
  · obtain ⟨i, hi, rfl⟩ := hx
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul hi Submodule.mem_top
  · rw [add_smul]; exact Submodule.add_mem _ (hx y) (hx' y)
  · rw [smul_eq_mul, mul_comm, mul_smul]; exact hx _
open CategoryTheory CategoryTheory.Limits TensorProduct in
private theorem mem_ideal_smul_of_mem_map_smul {V A N : Type*} [CommRing V] [CommRing A]
    [Algebra V A] [AddCommGroup N] [Module A N] [Module V N] [IsScalarTower V A N] (I : Ideal V)
    (K : Submodule A N) {w : N} (hw : w ∈ I.map (algebraMap V A) • K) :
    w ∈ I • (⊤ : Submodule V N) := by
  exact Submodule.smul_induction_on (p := fun w => w ∈ I • (⊤ : Submodule V N)) hw
    (fun r hr y _ => smul_mem_ideal_smul_of_mem_map I hr y)
    (fun x y hx hy => Submodule.add_mem _ hx hy)
open CategoryTheory CategoryTheory.Limits TensorProduct in
private theorem mem_ideal_smul_of_smul_mem_of_flat {V N : Type*} [CommRing V] [IsNoetherianRing V]
    [AddCommGroup N] [Module V N] [Module.Flat V N] (J m : Ideal V) (a : V)
    (ha : ∀ b, a * b ∈ J → b ∈ m) {n : N} (hn : a • n ∈ J • (⊤ : Submodule V N)) :
    n ∈ m • (⊤ : Submodule V N) := by
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian J)
  rw [← hg] at hn
  obtain ⟨k, -, hk⟩ := exists_sum_smul_of_mem_span_range_smul' g ⊤ hn
  have hrel : ∑ i : Fin (r + 1), (Fin.cons a (fun i => -g i) : Fin (r + 1) → V) i •
      (Fin.cons n k : Fin (r + 1) → N) i = 0 := by
    rw [Fin.sum_univ_succ]
    simp [hk, neg_smul, Finset.sum_neg_distrib]
  obtain ⟨p, b, y, hx, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  have h0 := hx 0
  simp only [Fin.cons_zero] at h0
  rw [h0]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (ha _ ?_) Submodule.mem_top
  have h1 := hb j
  rw [Fin.sum_univ_succ] at h1
  simp only [Fin.cons_zero, Fin.cons_succ, neg_mul, Finset.sum_neg_distrib] at h1
  have he : a * b 0 j = ∑ i, g i * b i.succ j := by linear_combination h1
  rw [he, ← hg]
  exact Submodule.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Submodule.subset_span ⟨i, rfl⟩)
open CategoryTheory CategoryTheory.Limits TensorProduct in
private theorem mem_map_smul_of_maximalIdeal_pow_le {V A N : Type*} [CommRing V] [IsNoetherianRing V]
    [IsLocalRing V] [CommRing A] [Algebra V A] [AddCommGroup N] [Module A N] [Module V N]
    [IsScalarTower V A N] [Module.Flat V N] (K : Submodule A N)
    (h0 : ∀ z ∈ K, z ∈ IsLocalRing.maximalIdeal V • (⊤ : Submodule V N) →
      z ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V A) • K)
    (p : ℕ) (J : Ideal V) (hJ : IsLocalRing.maximalIdeal V ^ p ≤ J) :
    ∀ z ∈ K, z ∈ J • (⊤ : Submodule V N) → z ∈ J.map (algebraMap V A) • K := by
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro z hz hzJ
  by_cases htop : J = ⊤
  · subst htop
    rw [Ideal.map_top, Submodule.top_smul]
    exact hz
  classical
  have hex : ∃ k, IsLocalRing.maximalIdeal V ^ k ≤ J := ⟨p, hJ⟩
  have hk : IsLocalRing.maximalIdeal V ^ Nat.find hex ≤ J := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    apply htop
    rw [h, pow_zero, Ideal.one_eq_top] at hk
    exact top_le_iff.1 hk
  have hk1 : ¬ IsLocalRing.maximalIdeal V ^ (Nat.find hex - 1) ≤ J :=
    Nat.find_min hex (by omega)
  obtain ⟨a, ha, haJ⟩ := SetLike.not_le_iff_exists.1 hk1
  have hma : ∀ b ∈ IsLocalRing.maximalIdeal V, a * b ∈ J := by
    intro b hb
    apply hk
    have : IsLocalRing.maximalIdeal V ^ Nat.find hex =
        IsLocalRing.maximalIdeal V ^ (Nat.find hex - 1) * IsLocalRing.maximalIdeal V := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this]
    exact Ideal.mul_mem_mul ha hb
  have hcol : ∀ b, a * b ∈ J → b ∈ IsLocalRing.maximalIdeal V := by
    intro b hb
    by_contra hbm
    have hu : IsUnit b := by
      by_contra h'
      exact hbm ((IsLocalRing.mem_maximalIdeal b).2 h')
    apply haJ
    have h2 := J.mul_mem_right (↑hu.unit⁻¹ : V) hb
    rwa [mul_assoc, hu.mul_val_inv, mul_one] at h2
  have hlt : J < J ⊔ Ideal.span {a} := by
    refine lt_of_le_of_ne le_sup_left fun h => haJ ?_
    rw [h]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have hz' := ih _ hlt (hJ.trans le_sup_left) z hz (Submodule.smul_mono_left le_sup_left hzJ)
  rw [Ideal.map_sup, Submodule.sup_smul, Ideal.map_span, Set.image_singleton,
    Submodule.ideal_span_singleton_smul] at hz'
  obtain ⟨w, hw, v, hv, rfl⟩ := Submodule.mem_sup.1 hz'
  obtain ⟨c, hc, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
  have hac : a • c ∈ J • (⊤ : Submodule V N) := by
    have h1 := Submodule.sub_mem _ hzJ (mem_ideal_smul_of_mem_map_smul J K hw)
    rwa [add_sub_cancel_left, algebraMap_smul] at h1
  have hcm := h0 c hc (mem_ideal_smul_of_smul_mem_of_flat J _ a hcol hac)
  have key : ∀ c' ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V A) • K,
      algebraMap V A a • c' ∈ J.map (algebraMap V A) • K := by
    intro c' hc'
    refine Submodule.smul_induction_on
      (p := fun c' => algebraMap V A a • c' ∈ J.map (algebraMap V A) • K) hc'
      (fun r hr y hy => ?_) (fun x y hx hy => ?_)
    · rw [smul_smul]
      refine Submodule.smul_mem_smul ?_ hy
      have hle : (Ideal.span {a} * IsLocalRing.maximalIdeal V).map (algebraMap V A) ≤
          J.map (algebraMap V A) :=
        Ideal.map_mono (Ideal.mul_le.2 fun x hx b hb => by
          obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hx
          rw [mul_assoc]
          exact J.mul_mem_left _ (hma b hb))
      rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hle
      exact hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hr)
    · rw [smul_add]; exact Submodule.add_mem _ hx hy
  exact Submodule.add_mem _ hw (key c hcm)
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] (M N : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup N] [Module A N] [Module V N] [IsScalarTower V A N] [Module.Flat V N] (u : M →ₗ[A] N), (∀ x : M, u x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A N) → x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A M)) → Module.Flat V (N ⧸ LinearMap.range u) := by
  intro V A _ _ _ _ _ _ _ _ M N _ _ _ _ _ _ _ _ u hu
  have hmA : (IsLocalRing.maximalIdeal V).map (algebraMap V A) ≠ ⊤ := by
    intro h
    have hle : (IsLocalRing.maximalIdeal V).map (algebraMap V A) ≤ IsLocalRing.maximalIdeal A :=
      Ideal.map_le_iff_le_comap.2 fun x hx => by
        rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun h' => (IsLocalRing.mem_maximalIdeal x).1 hx (isUnit_of_map_unit _ _ h')
    rw [h] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.1 hle)
  have hgen : ∀ y ∈ IsLocalRing.maximalIdeal V • (⊤ : Submodule V N),
      y ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V A) • (⊤ : Submodule A N) := by
    intro y hy
    refine Submodule.smul_induction_on
      (p := fun y => y ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V A) • (⊤ : Submodule A N))
      hy (fun r hr y _ => ?_) (fun x y hx hy => Submodule.add_mem _ hx hy)
    rw [← algebraMap_smul A r y]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  have hgen2 : ∀ y ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V A) • (⊤ : Submodule A M),
      u y ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V A) • LinearMap.range u := by
    intro y hy
    refine Submodule.smul_induction_on
      (p := fun y => u y ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V A) • LinearMap.range u)
      hy (fun r hr y _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul]
      exact Submodule.smul_mem_smul hr (LinearMap.mem_range_self u y)
    · rw [map_add]; exact Submodule.add_mem _ hx hy
  have h0 : ∀ z ∈ LinearMap.range u, z ∈ IsLocalRing.maximalIdeal V • (⊤ : Submodule V N) →
      z ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V A) • LinearMap.range u := by
    rintro _ ⟨x, rfl⟩ hx
    exact hgen2 x (hu x (hgen _ hx))
  refine flat_quotient_of_mem_ideal_smul_imp_mem_map_smul (LinearMap.range u) fun I z hz hzI => ?_
  let K := LinearMap.range u
  let P : Submodule A K := (I.map (algebraMap V A) • K).comap K.subtype
  have hstep : ∀ p : ℕ, Submodule.Quotient.mk (p := P) ⟨z, hz⟩ ∈
      (IsLocalRing.maximalIdeal V).map (algebraMap V A) ^ p • (⊤ : Submodule A (K ⧸ P)) := by
    intro p
    have h1 := mem_map_smul_of_maximalIdeal_pow_le K h0 p (I ⊔ IsLocalRing.maximalIdeal V ^ p) le_sup_right
      z hz (Submodule.smul_mono_left le_sup_left hzI)
    rw [Ideal.map_sup, Submodule.sup_smul, Ideal.map_pow] at h1
    obtain ⟨l, hl, w, hw, hlw⟩ := Submodule.mem_sup.1 h1
    have hw' : w ∈ ((IsLocalRing.maximalIdeal V).map (algebraMap V A) ^ p •
        (⊤ : Submodule A K)).map K.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
      exact hw
    obtain ⟨w', hw'', rfl⟩ := hw'
    have heq : Submodule.Quotient.mk (p := P) ⟨z, hz⟩ = Submodule.Quotient.mk w' := by
      rw [Submodule.Quotient.eq]
      show z - (w' : N) ∈ I.map (algebraMap V A) • K
      rw [← hlw]
      simpa using hl
    rw [heq]
    have hle : ((IsLocalRing.maximalIdeal V).map (algebraMap V A) ^ p •
        (⊤ : Submodule A K)).map P.mkQ ≤
        (IsLocalRing.maximalIdeal V).map (algebraMap V A) ^ p • (⊤ : Submodule A (K ⧸ P)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hle (Submodule.mem_map_of_mem hw'')
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := K ⧸ P)
    ((IsLocalRing.maximalIdeal V).map (algebraMap V A)) hmA
  have hmem : Submodule.Quotient.mk (p := P) ⟨z, hz⟩ ∈
      (⨅ i, (IsLocalRing.maximalIdeal V).map (algebraMap V A) ^ i • ⊤ : Submodule A (K ⧸ P)) :=
    Submodule.mem_iInf _ |>.2 hstep
  rw [hbot, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
  exact hmem
end _root_.GlobalTheory
end GlobalTheory
