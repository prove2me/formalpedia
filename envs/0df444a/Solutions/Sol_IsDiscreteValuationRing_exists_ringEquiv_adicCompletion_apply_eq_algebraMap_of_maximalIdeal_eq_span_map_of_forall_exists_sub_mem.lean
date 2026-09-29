-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_maximalIdeal_eq_span_map_of_forall_exists_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8db1b662-60ea-52a6-ae89-1f50fc3d051a

import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_maximalIdeal_eq_span_map_of_forall_exists_sub_mem

set_option autoImplicit false

open IsLocalRing

set_option linter.unusedSectionVars false

namespace Submodule p2m_export "Submodule" "Quotient.eq mk smul_mem mem_bot mem_span_singleton_self Quotient.mk span smul_induction_on mem_map_of_mem add_mem_sup mem_span_range_iff_exists_fun mem_top mem_span_singleton fg_iff_exists_fin_generating_family mul_mem_mul smul_mem_smul generators map_smul' zero one map_span map rec mem_sup subset_span smul_def FG ext factor_mk span_singleton_eq_bot comap factorPow fg_span map_le_iff_le_comap restrictScalars_mem" end Submodule
p2m_open_scoped "Submodule" in
theorem Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) [IsAdicComplete I A] [IsHausdorff I M]
    (N : Submodule A M) (hN : N.FG) (h : N ⊔ I • ⊤ = ⊤) : N = ⊤ := by
  classical
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hN

  let φ : (Fin k → A) →ₗ[A] M :=
    { toFun := fun c => ∑ i, c i • s i
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.smul_sum, mul_smul] }
  have hφ : ∀ c, φ c = ∑ i, c i • s i := fun c => rfl
  have hφN : ∀ c, φ c ∈ N := fun c => by
    rw [hφ, ← hs]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have h0 : ∀ m : M, ∃ c : Fin k → A, m - φ c ∈ (I • ⊤ : Submodule A M) := fun m => by
    have hm : m ∈ N ⊔ I • ⊤ := by rw [h]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hm
    rw [← hs, Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, rfl⟩ := hy
    exact ⟨c, by rw [hφ]; simpa using hz⟩

  have hstep : ∀ (n : ℕ) (y : M), y ∈ (I ^ n • ⊤ : Submodule A M) →
      ∃ c : Fin k → A, (∀ i, c i ∈ I ^ n) ∧ y - φ c ∈ (I ^ (n + 1) • ⊤ : Submodule A M) := by
    intro n y hy
    refine Submodule.smul_induction_on
      (p := fun y => ∃ c : Fin k → A, (∀ i, c i ∈ I ^ n) ∧ y - φ c ∈ (I ^ (n + 1) • ⊤ : Submodule A M))
      hy ?_ ?_
    · intro r hr m _
      obtain ⟨c, hc⟩ := h0 m
      refine ⟨r • c, fun i => Ideal.mul_mem_right _ _ hr, ?_⟩
      rw [map_smul, ← smul_sub, pow_succ, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hr hc
    · rintro y₁ y₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
      refine ⟨c₁ + c₂, fun i => Ideal.add_mem _ (hc₁ i) (hc₂ i), ?_⟩
      rw [map_add]
      convert Submodule.add_mem _ h₁ h₂ using 1
      abel
  choose c hcI hcy using hstep
  refine eq_top_iff.mpr fun x _ => ?_

  let r : (n : ℕ) → {y : M // y ∈ (I ^ n • ⊤ : Submodule A M)} :=
    fun n => Nat.rec (motive := fun n => {y : M // y ∈ (I ^ n • ⊤ : Submodule A M)})
      ⟨x, by simp⟩ (fun n y => ⟨y.1 - φ (c n y.1 y.2), hcy n y.1 y.2⟩) n

  let a : ℕ → Fin k → A := fun n => c n (r n).1 (r n).2
  have haI : ∀ n i, a n i ∈ I ^ n := fun n i => hcI n (r n).1 (r n).2 i
  let S : ℕ → Fin k → A := fun n i => ∑ t ∈ Finset.range n, a t i
  have hS0 : S 0 = 0 := funext fun i => by simp [S]
  have hSsucc : ∀ n, S (n + 1) = S n + a n := fun n => funext fun i => by
    simp [S, Finset.sum_range_succ]
  have hr0 : (r 0).1 = x := rfl
  have hrsucc : ∀ n, (r (n + 1)).1 = (r n).1 - φ (a n) := fun n => rfl
  have hr : ∀ n, (r n).1 = x - φ (S n) := by
    intro n
    induction n with
    | zero => rw [hr0, hS0, map_zero, sub_zero]
    | succ n ih => rw [hrsucc, ih, hSsucc, map_add]; abel

  have hS : ∀ i m n, m ≤ n → S n i - S m i ∈ I ^ m := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hSsucc, Pi.add_apply, add_sub_right_comm]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmn (haI n i))
  have hL : ∀ i, ∃ L : A, ∀ n, S n i - L ∈ I ^ n := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I A) (f := fun n => S n i)
      (fun {m n} hmn => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, Ideal.neg_mem_iff]
        exact hS i m n hmn)
    exact ⟨L, fun n => by simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL n⟩
  choose L hL using hL

  suffices hx : x - φ L = 0 by rw [sub_eq_zero.mp hx]; exact hφN L
  refine IsHausdorff.haus (inferInstance : IsHausdorff I M) _ fun n => ?_
  rw [SModEq.zero]
  have : x - φ L = (r n).1 + φ (S n - L) := by rw [hr n, map_sub]; abel
  rw [this]
  refine Submodule.add_mem _ (r n).2 ?_
  rw [hφ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hL i n) Submodule.mem_top

namespace B16CR

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
  {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  (σ : A →+* W) (hσ : maximalIdeal W = Ideal.span {σ ϖ})

local notation "Â" => AdicCompletion (maximalIdeal A) A

include hϖ hσ in
theorem map_maximalIdeal : (maximalIdeal A).map σ = maximalIdeal W := by
  rw [hϖ, hσ, Ideal.map_span, Set.image_singleton]

include hϖ hσ in
private theorem _root_.B16CR.map_pow (n : ℕ) : ((maximalIdeal A) ^ n).map σ = (maximalIdeal W) ^ n := by
  rw [Ideal.map_pow, map_maximalIdeal ϖ hϖ σ hσ]

p2m_export "B16CR" "map_pow"
include hϖ hσ in
theorem pow_le_comap (n : ℕ) : (maximalIdeal A) ^ n ≤ ((maximalIdeal W) ^ n).comap σ := by
  rw [← Ideal.map_le_iff_le_comap, map_pow ϖ hϖ σ hσ n]

noncomputable def f (n : ℕ) : Â →+* W ⧸ (maximalIdeal W) ^ n :=
  (Ideal.quotientMap ((maximalIdeal W) ^ n) σ (pow_le_comap ϖ hϖ σ hσ n)).comp
    (AdicCompletion.evalₐ (maximalIdeal A) n : Â →+* A ⧸ (maximalIdeal A) ^ n)

theorem f_mk (n : ℕ) (x : AdicCompletion.AdicCauchySequence (maximalIdeal A) A) :
    f ϖ hϖ σ hσ n (AdicCompletion.mk (maximalIdeal A) A x) = Ideal.Quotient.mk _ (σ (x.val n)) := by
  simp only [f, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AdicCompletion.evalₐ_mk,
    Ideal.quotientMap_mk]

theorem f_of (n : ℕ) (a : A) :
    f ϖ hϖ σ hσ n (AdicCompletion.of (maximalIdeal A) A a) = Ideal.Quotient.mk _ (σ a) := by
  simp only [f, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AdicCompletion.evalₐ_of,
    Ideal.quotientMap_mk]

theorem f_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal W) hle).comp (f ϖ hϖ σ hσ n) = f ϖ hϖ σ hσ m := by
  ext x
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal A) A x
  rw [RingHom.comp_apply, f_mk, f_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq,
    ← map_sub]
  have h := x.2 hle
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  have h' : x.val n - x.val m ∈ (maximalIdeal A) ^ m := by
    rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 h
  have := Ideal.mem_map_of_mem σ h'
  rwa [map_pow ϖ hϖ σ hσ m] at this

noncomputable def σhat : Â →+* W :=
  IsAdicComplete.liftRingHom (maximalIdeal W) (f ϖ hϖ σ hσ) (fun hle => f_compat ϖ hϖ σ hσ hle)

theorem eq_of_forall_sub_mem {a b : W} (h : ∀ n, a - b ∈ (maximalIdeal W) ^ n) : a = b := by
  refine sub_eq_zero.mp (IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal W) W) _ fun n => ?_)
  rw [SModEq.zero]
  simpa [smul_eq_mul, Ideal.mul_top] using h n

theorem σhat_of (a : A) : σhat ϖ hϖ σ hσ (AdicCompletion.of (maximalIdeal A) A a) = σ a := by
  apply eq_of_forall_sub_mem
  intro n
  rw [← Ideal.Quotient.eq]
  simp only [σhat, IsAdicComplete.mk_liftRingHom, f_of]

theorem σhat_algebraMap (a : A) : σhat ϖ hϖ σ hσ (algebraMap A Â a) = σ a := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, σhat_of]

theorem σhat_comp : (σhat ϖ hϖ σ hσ).comp (algebraMap A Â) = σ :=
  RingHom.ext (σhat_algebraMap ϖ hϖ σ hσ)

theorem map_map_pow (n : ℕ) :
    (((maximalIdeal A) ^ n).map (algebraMap A Â)).map (σhat ϖ hϖ σ hσ) = (maximalIdeal W) ^ n := by
  rw [Ideal.map_map, σhat_comp, map_pow ϖ hϖ σ hσ]

include hϖ hσ in

theorem mem_pow_of_map_mem_pow : ∀ (n : ℕ) (a : A), σ a ∈ (maximalIdeal W) ^ n → a ∈ (maximalIdeal A) ^ n := by
  have hϖW : σ ϖ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field W
    rw [hσ, h, Ideal.span_singleton_eq_bot]
  intro n
  induction n with
  | zero => intro a _; rw [pow_zero, Ideal.one_eq_top]; trivial
  | succ n ih =>
    intro a ha
    have haI : a ∈ maximalIdeal A := by
      by_contra hunit
      have hu : IsUnit a := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hunit
      have : σ a ∈ maximalIdeal W := Ideal.pow_le_self (Nat.succ_ne_zero n) ha
      exact ((mem_maximalIdeal _).1 this) (hu.map σ)
    rw [hϖ, Ideal.mem_span_singleton'] at haI
    obtain ⟨a', rfl⟩ := haI
    rw [hσ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha

    have h2 : σ a' = c * σ ϖ ^ n := by
      have : (c * σ ϖ ^ n) * σ ϖ = σ a' * σ ϖ := by rw [← map_mul, ← hc]; ring
      exact (mul_right_cancel₀ hϖW this).symm
    have ha' : a' ∈ (maximalIdeal A) ^ n := by
      apply ih
      rw [hσ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
      exact ⟨c, h2.symm⟩
    rw [pow_succ]
    exact Ideal.mul_mem_mul ha' (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)

theorem σhat_injective : Function.Injective (σhat ϖ hϖ σ hσ) := by
  have hI : (maximalIdeal A).FG := IsNoetherian.noetherian _
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [Submodule.mem_bot]
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [map_zero]
  obtain ⟨a, y, hy, rfl⟩ := AdicCompletion.exists_eq_algebraMap_add (maximalIdeal A) hI n x
  have hσy : σhat ϖ hϖ σ hσ y ∈ (maximalIdeal W) ^ n := by
    rw [← map_map_pow ϖ hϖ σ hσ n]; exact Ideal.mem_map_of_mem _ hy
  rw [map_add, σhat_algebraMap] at hx
  have hσa : σ a ∈ (maximalIdeal W) ^ n := by
    have : σ a = -σhat ϖ hϖ σ hσ y := eq_neg_of_add_eq_zero_left hx
    rw [this]; exact (Ideal.neg_mem_iff _).2 hσy
  have ha := mem_pow_of_map_mem_pow ϖ hϖ σ hσ n a hσa
  have : algebraMap A Â a + y ∈ ((maximalIdeal A) ^ n).map (algebraMap A Â) :=
    Ideal.add_mem _ (Ideal.mem_map_of_mem _ ha) hy
  rw [← AdicCompletion.ker_evalₐ_eq_map_pow _ hI n, RingHom.mem_ker] at this
  exact this

theorem σhat_surjective (hres : ∀ w : W, ∃ a : A, w - σ a ∈ maximalIdeal W) :
    Function.Surjective (σhat ϖ hϖ σ hσ) := by
  have hI : (maximalIdeal A).FG := IsNoetherian.noetherian _
  let ρ' : Â →+* W := σhat ϖ hϖ σ hσ
  letI : Algebra Â W := ρ'.toAlgebra
  have halg : algebraMap Â W = ρ' := rfl
  let K : Ideal Â := (maximalIdeal A).map (algebraMap A Â)
  haveI : IsAdicComplete (maximalIdeal A) Â := AdicCompletion.isAdicComplete hI
  haveI : IsAdicComplete K Â := (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance
  have hKn : ∀ n, (K ^ n).map ρ' = (maximalIdeal W) ^ n := fun n => by
    rw [← Ideal.map_pow]; exact map_map_pow ϖ hϖ σ hσ n
  haveI : IsHausdorff K W := by
    refine ⟨fun x hx => ?_⟩
    apply IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal W) W)
    intro n
    have hn := hx n
    rw [SModEq.zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, halg, hKn] at hn
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hn
  let N : Submodule Â W := Submodule.span Â {1}
  have hN : N.FG := Submodule.fg_span (Set.toFinite _)
  have key : N ⊔ K • ⊤ = ⊤ := by
    rw [eq_top_iff]
    rintro w -
    obtain ⟨a, ha⟩ := hres w
    have h2 : w - σ a ∈ (K • ⊤ : Submodule Â W) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, halg, ← pow_one K, hKn, pow_one]
      exact ha
    have h3 : σ a ∈ N := by
      rw [Submodule.mem_span_singleton]
      refine ⟨algebraMap A Â a, ?_⟩
      rw [Algebra.smul_def, halg, mul_one]
      exact σhat_algebraMap ϖ hϖ σ hσ a
    have : w = σ a + (w - σ a) := by ring
    rw [this]
    exact Submodule.add_mem_sup h3 h2
  have hNtop := Submodule.eq_top_of_isAdicComplete_of_fg_of_sup_smul_eq_top K N hN key
  intro y
  have hy : y ∈ N := hNtop ▸ Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hy
  obtain ⟨b, rfl⟩ := hy
  exact ⟨b, by rw [Algebra.smul_def, halg, mul_one]⟩

end B16CR

theorem solution
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (σ : A →+* W) (hσ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (hres : ∀ w : W, ∃ a : A, w - σ a ∈ IsLocalRing.maximalIdeal W) :
    ∃ ρ : W ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A,
      ∀ a : A, ρ (σ a) = algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a := by
  classical
  let e := RingEquiv.ofBijective (B16CR.σhat ϖ hϖ σ hσ)
    ⟨B16CR.σhat_injective ϖ hϖ σ hσ, B16CR.σhat_surjective ϖ hϖ σ hσ hres⟩
  refine ⟨e.symm, fun a => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  exact (B16CR.σhat_algebraMap ϖ hϖ σ hσ a).symm

end S_IsDiscreteValuationRing_exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_maximalIdeal_eq_span_map_of_forall_exists_sub_mem
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_maximalIdeal_eq_span_map_of_forall_exists_sub_mem (solution)
