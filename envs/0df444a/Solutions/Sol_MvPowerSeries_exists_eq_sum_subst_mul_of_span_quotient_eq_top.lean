-- Prove2me | solution 1 for MvPowerSeries.exists_eq_sum_subst_mul_of_span_quotient_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6ce51504-1b76-51ea-b25a-8ecf79c9858a

import Mathlib
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top

set_option autoImplicit false

open MvPowerSeries

namespace SurjApprox

section CN

variable {R : Type} [CommRing R] (I : Ideal R) {M : Type} [AddCommGroup M] [Module R M]

theorem smul_top_pow_succ (k : ℕ) : I ^ k • (I • (⊤ : Submodule R M)) = I ^ (k + 1) • ⊤ := by
  rw [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ]

theorem step {d : ℕ} (m : Fin d → M)
    (hgen : ∀ x : M, ∃ a : Fin d → R, x - ∑ j, a j • m j ∈ I • (⊤ : Submodule R M))
    (k : ℕ) (x : M) (hx : x ∈ I ^ k • (⊤ : Submodule R M)) :
    ∃ a : Fin d → R, (∀ j, a j ∈ I ^ k) ∧ x - ∑ j, a j • m j ∈ I ^ (k + 1) • (⊤ : Submodule R M) := by
  classical
  induction hx using Submodule.smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨a, ha⟩ := hgen y
    refine ⟨fun j => r * a j, fun j => Ideal.mul_mem_right _ _ hr, ?_⟩
    have : r • y - ∑ j, (r * a j) • m j = r • (y - ∑ j, a j • m j) := by
      rw [smul_sub, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => (smul_smul r (a j) (m j)).symm
    rw [this, ← smul_top_pow_succ]
    exact Submodule.smul_mem_smul hr ha
  | add x hx y hy ihx ihy =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨a', ha', hay⟩ := ihy
    refine ⟨a + a', fun j => Ideal.add_mem _ (ha j) (ha' j), ?_⟩
    have : x + y - ∑ j, (a + a') j • m j = (x - ∑ j, a j • m j) + (y - ∑ j, a' j • m j) := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel
    rw [this]
    exact Submodule.add_mem _ hax hay

theorem exists_eq_sum_smul [IsAdicComplete I R] [IsHausdorff I M] {d : ℕ} (m : Fin d → M)
    (hgen : ∀ x : M, ∃ a : Fin d → R, x - ∑ j, a j • m j ∈ I • (⊤ : Submodule R M)) (x : M) :
    ∃ c : Fin d → R, x = ∑ j, c j • m j := by
  classical
  have hstep : ∀ (k : ℕ) (z : {z : M // z ∈ I ^ k • (⊤ : Submodule R M)}),
      ∃ a : Fin d → R, (∀ j, a j ∈ I ^ k) ∧ z.1 - ∑ j, a j • m j ∈ I ^ (k + 1) • (⊤ : Submodule R M) :=
    fun k z => step I m hgen k z.1 z.2
  choose A hAI hAnext using hstep
  let seq : (k : ℕ) → {z : M // z ∈ I ^ k • (⊤ : Submodule R M)} :=
    fun k => Nat.rec (motive := fun k => {z : M // z ∈ I ^ k • (⊤ : Submodule R M)})
      ⟨x, by rw [pow_zero, one_smul]; exact Submodule.mem_top⟩
      (fun k z => ⟨z.1 - ∑ j, A k z j • m j, hAnext k z⟩) k
  have hseq0 : (seq 0).1 = x := rfl
  have hseqS : ∀ k, (seq (k + 1)).1 = (seq k).1 - ∑ j, A k (seq k) j • m j := fun k => rfl
  let a : ℕ → Fin d → R := fun k => A k (seq k)
  have haI : ∀ k j, a k j ∈ I ^ k := fun k j => hAI k (seq k) j
  let s : ℕ → Fin d → R := fun K j => ∑ k ∈ Finset.range K, a k j
  have hpartial : ∀ K, x = ∑ j, s K j • m j + (seq K).1 := by
    intro K
    induction K with
    | zero => simp [s, hseq0]
    | succ K ih =>
      rw [hseqS, ih]
      simp only [s, Finset.sum_range_succ, add_smul, Finset.sum_add_distrib]
      abel
  have hcauchy : ∀ j, ∀ {m' n' : ℕ}, m' ≤ n' → s m' j ≡ s n' j [SMOD (I ^ m' • ⊤ : Submodule R R)] := by
    intro j m' n' hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have : s m' j - s n' j = -∑ k ∈ Finset.Ico m' n', a k j := by
      simp only [s]
      rw [← Finset.sum_range_add_sum_Ico _ hmn]
      abel
    rw [this, neg_mem_iff]
    exact Ideal.sum_mem _ fun k hk => Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1 (haI k j)
  have hlim : ∀ j, ∃ c : R, ∀ K, s K j ≡ c [SMOD (I ^ K • ⊤ : Submodule R R)] :=
    fun j => IsPrecomplete.prec' _ (hcauchy j)
  choose c hc using hlim
  refine ⟨c, ?_⟩
  apply eq_of_sub_eq_zero
  refine IsHausdorff.haus' (I := I) _ fun K => ?_
  rw [SModEq.sub_mem, sub_zero]
  have hdiff : x - ∑ j, c j • m j = (seq K).1 - ∑ j, (c j - s K j) • m j := by
    conv_lhs => rw [hpartial K]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hdiff]
  refine Submodule.sub_mem _ (seq K).2 (Submodule.sum_mem _ fun j _ => ?_)
  have hcj : c j - s K j ∈ I ^ K := by
    have := (hc j K).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  exact Submodule.smul_mem_smul hcj Submodule.mem_top

end CN

section ViaRho

variable {B : Type} [CommRing B] {n : ℕ}

def ViaRho (ρ : Fin n → MvPowerSeries (Fin n) B) (_hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0) : Type :=
  MvPowerSeries (Fin n) B

variable (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)

noncomputable scoped instance : AddCommGroup (ViaRho ρ hρ0) := inferInstanceAs (AddCommGroup (MvPowerSeries (Fin n) B))

noncomputable def toV : MvPowerSeries (Fin n) B ≃+ ViaRho ρ hρ0 := AddEquiv.refl _

include hρ0 in
theorem subst_one' : MvPowerSeries.subst ρ (1 : MvPowerSeries (Fin n) B) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0), map_one]

include hρ0 in
theorem subst_mul' (a c : MvPowerSeries (Fin n) B) :
    MvPowerSeries.subst ρ (a * c) = MvPowerSeries.subst ρ a * MvPowerSeries.subst ρ c := by
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0), map_mul]

include hρ0 in
theorem subst_add' (a c : MvPowerSeries (Fin n) B) :
    MvPowerSeries.subst ρ (a + c) = MvPowerSeries.subst ρ a + MvPowerSeries.subst ρ c := by
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0), map_add]

include hρ0 in
theorem subst_zero' : MvPowerSeries.subst ρ (0 : MvPowerSeries (Fin n) B) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0), map_zero]

noncomputable scoped instance instModule : Module (MvPowerSeries (Fin n) B) (ViaRho ρ hρ0) where
  smul c f := toV ρ hρ0 (MvPowerSeries.subst ρ c * (toV ρ hρ0).symm f)
  one_smul f := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ 1 * (toV ρ hρ0).symm f) = f
    rw [subst_one' ρ hρ0, one_mul]; rfl
  mul_smul a c f := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ (a * c) * (toV ρ hρ0).symm f) =
      toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm (toV ρ hρ0 (MvPowerSeries.subst ρ c * (toV ρ hρ0).symm f)))
    rw [subst_mul' ρ hρ0, AddEquiv.symm_apply_apply, mul_assoc]
  smul_zero a := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm 0) = 0
    rw [map_zero, mul_zero, map_zero]
  smul_add a f g := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm (f + g)) =
      toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm f) + toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm g)
    rw [map_add, mul_add, map_add]
  add_smul a c f := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ (a + c) * (toV ρ hρ0).symm f) =
      toV ρ hρ0 (MvPowerSeries.subst ρ a * (toV ρ hρ0).symm f) + toV ρ hρ0 (MvPowerSeries.subst ρ c * (toV ρ hρ0).symm f)
    rw [subst_add' ρ hρ0, add_mul, map_add]
  zero_smul f := by
    change toV ρ hρ0 (MvPowerSeries.subst ρ 0 * (toV ρ hρ0).symm f) = 0
    rw [subst_zero' ρ hρ0, zero_mul, map_zero]

theorem smul_def (c : MvPowerSeries (Fin n) B) (f : ViaRho ρ hρ0) :
    c • f = toV ρ hρ0 (MvPowerSeries.subst ρ c * (toV ρ hρ0).symm f) := rfl

end ViaRho

section Low

variable {σ : Type} {R : Type} [CommRing R]

def lowVanishing (σ : Type) (R : Type) [CommRing R] (N : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {q | ∀ d : σ →₀ ℕ, d.degree < N → MvPowerSeries.coeff d q = 0}
  add_mem' {a b} ha hb := fun d hd => by rw [map_add, ha d hd, hb d hd, add_zero]
  zero_mem' := fun d _ => by simp
  smul_mem' c {q} hq := fun d hd => by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have : x.2.degree < N := by
      have h := congrArg Finsupp.degree hx'
      rw [map_add] at h
      omega
    rw [hq x.2 this, mul_zero]

theorem span_X_le_lowVanishing_one :
    Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ≤ lowVanishing σ R 1 := by
  classical
  rw [Ideal.span_le]
  rintro _ ⟨s, rfl⟩ d hd
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
  subst this
  exact MvPowerSeries.coeff_zero_X s

theorem lowVanishing_mul_le (a b : ℕ) : lowVanishing σ R a * lowVanishing σ R b ≤ lowVanishing σ R (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro p hp q hq d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)
  rw [map_add] at hx'
  by_cases h1 : x.1.degree < a
  · rw [hp x.1 h1, zero_mul]
  · have h2 : x.2.degree < b := by omega
    rw [hq x.2 h2, mul_zero]

theorem pow_span_X_le_lowVanishing (N : ℕ) :
    Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ N ≤ lowVanishing σ R N := by
  induction N with
  | zero =>
    intro q _ d hd
    exact absurd hd (Nat.not_lt_zero _)
  | succ N ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih span_X_le_lowVanishing_one).trans (lowVanishing_mul_le N 1)

theorem eq_zero_of_forall_mem_pow_span_X (q : MvPowerSeries σ R)
    (hq : ∀ N, q ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ N) : q = 0 := by
  ext d
  rw [map_zero]
  exact pow_span_X_le_lowVanishing (d.degree + 1) (hq _) d (Nat.lt_succ_self _)

end Low

end SurjApprox
p2m_reactivate "P2MW.S_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top.SurjApprox"

open SurjApprox in
theorem solution
    {B : Type} [CommRing B] {n d : ℕ} (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (b : Fin d → MvPowerSeries (Fin n) B)
    (hgen : Submodule.span B (Set.range (fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j))) = ⊤)
    (f : MvPowerSeries (Fin n) B) :
    ∃ c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j := by
  classical
  set I : Ideal (MvPowerSeries (Fin n) B) := Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) B)) with hI
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0

  have hρx : ∀ i, ρ i ∈ I := fun i => by
    have h := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 (ρ i) (fun m hm => by
      have : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
      subst this; exact hρ0 i)
    rwa [pow_one] at h

  have hmapI : ∀ k : ℕ, ∀ c ∈ I ^ k, MvPowerSeries.subst ρ c ∈ I ^ k := by
    intro k c hc
    let φ : MvPowerSeries (Fin n) B →+* MvPowerSeries (Fin n) B :=
      (MvPowerSeries.substAlgHom hsub : MvPowerSeries (Fin n) B →ₐ[B] _).toRingHom
    have hφ : ∀ g, φ g = MvPowerSeries.subst ρ g := fun g => by
      show (MvPowerSeries.substAlgHom hsub) g = _
      rw [← MvPowerSeries.coe_substAlgHom hsub]
    have h1 : I.map φ ≤ I := by
      rw [hI, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [hφ, MvPowerSeries.subst_X hsub]
      exact hρx i
    have h2 : (I ^ k).map φ ≤ I ^ k := by rw [Ideal.map_pow]; exact Ideal.pow_right_mono h1 k
    have h3 := h2 (Ideal.mem_map_of_mem φ hc)
    rwa [hφ] at h3

  have hsmul_le : ∀ (k : ℕ) (z : ViaRho ρ hρ0), z ∈ I ^ k • (⊤ : Submodule (MvPowerSeries (Fin n) B) (ViaRho ρ hρ0)) →
      (toV ρ hρ0).symm z ∈ I ^ k := by
    intro k z hz
    induction hz using Submodule.smul_induction_on' with
    | smul r hr y _ =>
      rw [smul_def ρ hρ0]
      change MvPowerSeries.subst ρ r * (toV ρ hρ0).symm y ∈ I ^ k
      exact Ideal.mul_mem_right _ _ (hmapI k r hr)
    | add x hx y hy ihx ihy =>
      change (toV ρ hρ0).symm x + (toV ρ hρ0).symm y ∈ I ^ k
      exact Ideal.add_mem _ ihx ihy
  haveI : IsHausdorff I (ViaRho ρ hρ0) := ⟨fun z hz => by
    have : (toV ρ hρ0).symm z = 0 := eq_zero_of_forall_mem_pow_span_X _ fun N => by
      have h := hz N
      rw [SModEq.sub_mem, sub_zero] at h
      exact hsmul_le N z h
    exact this⟩

  have hρI : ∀ w ∈ Ideal.span (Set.range ρ), toV ρ hρ0 w ∈ I • (⊤ : Submodule (MvPowerSeries (Fin n) B) (ViaRho ρ hρ0)) := by
    intro w hw
    obtain ⟨g, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hw
    change toV ρ hρ0 (∑ i, g i * ρ i) ∈ _
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : toV ρ hρ0 (g i * ρ i) = (MvPowerSeries.X i : MvPowerSeries (Fin n) B) • toV ρ hρ0 (g i) := by
      rw [smul_def ρ hρ0, MvPowerSeries.subst_X hsub, mul_comm]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) Submodule.mem_top

  have hgen' : ∀ z : ViaRho ρ hρ0, ∃ a : Fin d → MvPowerSeries (Fin n) B,
      z - ∑ j, a j • toV ρ hρ0 (b j) ∈ I • (⊤ : Submodule (MvPowerSeries (Fin n) B) (ViaRho ρ hρ0)) := by
    intro z
    have hmem : Ideal.Quotient.mk (Ideal.span (Set.range ρ)) ((toV ρ hρ0).symm z) ∈
        Submodule.span B (Set.range fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j)) := by
      rw [hgen]; exact Submodule.mem_top
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hmem
    refine ⟨fun j => (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B), ?_⟩
    have hdiff : (toV ρ hρ0).symm z - ∑ j, (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) * b j ∈ Ideal.span (Set.range ρ) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, sub_eq_zero, ← hβ]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : Ideal.Quotient.mkₐ B (Ideal.span (Set.range ρ)) ((MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) * b j) =
          β j • Ideal.Quotient.mkₐ B (Ideal.span (Set.range ρ)) (b j) := by
        rw [← MvPowerSeries.smul_eq_C_mul, map_smul]
      simpa only [Ideal.Quotient.mkₐ_eq_mk] using hj.symm
    have hsm : ∀ j, (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) • toV ρ hρ0 (b j) = toV ρ hρ0 ((MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) * b j) := fun j => by
      rw [smul_def ρ hρ0]
      congr 1
      have : MvPowerSeries.subst ρ ((MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) : MvPowerSeries (Fin n) B) = (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) := by
        rw [← MvPowerSeries.coe_substAlgHom hsub, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
      rw [this]
      rfl
    have : z - ∑ j, (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) • toV ρ hρ0 (b j) = toV ρ hρ0 ((toV ρ hρ0).symm z - ∑ j, (MvPowerSeries.C (β j) : MvPowerSeries (Fin n) B) * b j) := by
      rw [map_sub, map_sum, AddEquiv.apply_symm_apply]
      congr 1
      exact Finset.sum_congr rfl fun j _ => hsm j
    rw [this]
    exact hρI _ hdiff

  obtain ⟨c, hc⟩ := exists_eq_sum_smul I (fun j => toV ρ hρ0 (b j)) hgen' (toV ρ hρ0 f)
  refine ⟨c, ?_⟩
  apply (toV ρ hρ0).injective
  rw [hc, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_def ρ hρ0]; rfl

end S_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top
end P2MW
export P2MW.S_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top (solution)
