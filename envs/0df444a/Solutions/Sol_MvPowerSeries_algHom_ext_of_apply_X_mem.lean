-- Prove2me | solution 1 for MvPowerSeries.algHom_ext_of_apply_X_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/07d6ae56-3ed2-5399-a754-642391cdd431

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_algHom_ext_of_apply_X_mem

set_option autoImplicit false

universe u v w

namespace M4cP4PS

open MvPowerSeries IsLocalRing

section Vars

variable {σ : Type w} {R : Type u} [CommRing R]

theorem smodEq_pow_smul_top_iff (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

def dropVar (i : σ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if m i = 0 then φ m else 0

theorem coeff_dropVar (i : σ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (dropVar i φ) = if m i = 0 then coeff m φ else 0 := rfl

theorem mem_pow_span_X_of_coeff_eq_zero [Finite σ] (k : ℕ) (φ : MvPowerSeries σ R)
    (hφ : ∀ m : σ →₀ ℕ, m.degree < k → coeff m φ = 0) :
    φ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ k := by
  classical
  haveI := Fintype.ofFinite σ
  set J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) with hJ
  induction k generalizing φ with
  | zero => simp
  | succ k ihk =>

    suffices h : ∀ (s : Finset σ) (ψ : MvPowerSeries σ R), (∀ m : σ →₀ ℕ, m.degree < k + 1 → coeff m ψ = 0) →
        (∀ m : σ →₀ ℕ, ¬ (m.support ⊆ s) → coeff m ψ = 0) → ψ ∈ J ^ (k + 1) by
      exact h Finset.univ φ hφ fun m hm => (hm (Finset.subset_univ _)).elim
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro ψ h0 hs
      have : ψ = 0 := by
        ext m
        by_cases hm : m = 0
        · subst hm; rw [map_zero]; exact h0 0 (by simp)
        · rw [map_zero]
          refine hs m fun hsub => hm ?_
          ext j
          have : j ∉ m.support := fun hj => by simpa using hsub hj
          simpa [Finsupp.mem_support_iff] using this
      rw [this]; exact Ideal.zero_mem _
    | insert i s hi ih =>
      intro ψ h0 hs
      have hdiv : (X i : MvPowerSeries σ R) ∣ ψ - dropVar i ψ := by
        rw [X_dvd_iff]
        intro m hm
        rw [map_sub, coeff_dropVar, if_pos hm, sub_self]
      obtain ⟨q, hq⟩ := hdiv

      have hqk : ∀ m : σ →₀ ℕ, m.degree < k → coeff m q = 0 := by
        intro m hm
        have h1 : coeff (Finsupp.single i 1 + m) (X i * q) = coeff m q := by
          rw [X, coeff_add_monomial_mul, one_mul]
        have h2 : coeff (Finsupp.single i 1 + m) (ψ - dropVar i ψ) = 0 := by
          rw [map_sub, coeff_dropVar, if_neg (by simp), sub_zero]
          exact h0 _ (by rw [map_add, Finsupp.degree_single]; omega)
        rw [← h1, ← hq, h2]
      have hrest : dropVar i ψ ∈ J ^ (k + 1) := by
        refine ih _ ?_ ?_
        · intro m hm
          rw [coeff_dropVar]
          split_ifs
          · exact h0 m hm
          · rfl
        · intro m hm
          rw [coeff_dropVar]
          split_ifs with hmi
          · refine hs m fun hsub => hm fun j hj => ?_
            rcases Finset.mem_insert.mp (hsub hj) with rfl | h
            · exact absurd hmi (by simpa [Finsupp.mem_support_iff] using hj)
            · exact h
          · rfl
      have : ψ = dropVar i ψ + X i * q := by rw [← hq]; ring
      rw [this, pow_succ']
      exact Ideal.add_mem _ (pow_succ' J k ▸ hrest)
        (Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ihk q hqk))

theorem sub_truncTotal_mem_pow_span_X [Finite σ] (k : ℕ) (φ : MvPowerSeries σ R) :
    φ - (truncTotal k φ : MvPolynomial σ R) ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ k := by
  refine mem_pow_span_X_of_coeff_eq_zero k _ fun m hm => ?_
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hm, sub_self]

theorem map_pow_span_X_le {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]
    (φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (I : Ideal A) (hφ : ∀ i, φ (X i) ∈ I) (k : ℕ) :
    (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝒪)) ^ k).map φ ≤ I ^ k := by
  rw [Ideal.map_pow]
  refine Ideal.pow_right_mono ?_ k
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact hφ i

theorem algHom_apply_coe_eq {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]
    (φ ψ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (h : ∀ i, φ (X i) = ψ (X i)) (P : MvPolynomial σ 𝒪) :
    φ (P : MvPowerSeries σ 𝒪) = ψ (P : MvPowerSeries σ 𝒪) := by
  have : (φ.comp (MvPolynomial.coeToMvPowerSeries.algHom 𝒪)) =
      (ψ.comp (MvPolynomial.coeToMvPowerSeries.algHom 𝒪)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [h i]
  simpa using congrArg (fun f => f P) this

end Vars

section Construction

variable {σ : Type w} [Finite σ] (𝒪 : Type u) {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]
  (a : σ → A) (I : Ideal A) (ha : ∀ i, a i ∈ I)

include ha

omit [Finite σ] in
theorem idealOfVars_pow_le (k : ℕ) :
    MvPolynomial.idealOfVars σ 𝒪 ^ k ≤ (I ^ k).comap (MvPolynomial.aeval (R := 𝒪) a).toRingHom := by
  refine le_trans (Ideal.pow_right_mono ?_ k) (Ideal.le_comap_pow _ k)
  rw [MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simpa using ha i

noncomputable def evalTrunc (k : ℕ) : MvPowerSeries σ 𝒪 →+* A ⧸ I ^ k :=
  (Ideal.quotientMap (I ^ k) (MvPolynomial.aeval (R := 𝒪) a).toRingHom
    (idealOfVars_pow_le 𝒪 a I ha k)).comp (truncTotalAlgHom σ 𝒪 k).toRingHom

theorem evalTrunc_apply (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    evalTrunc 𝒪 a I ha k p = Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  simp [evalTrunc]

theorem evalTrunc_compat {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow I h).comp (evalTrunc 𝒪 a I ha l) = evalTrunc 𝒪 a I ha k := by
  ext p
  simp only [RingHom.coe_comp, Function.comp_apply, evalTrunc_apply, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact idealOfVars_pow_le 𝒪 a I ha k (truncTotal_sub_truncTotal_mem_pow_idealOfVars h le_rfl p)

variable [IsAdicComplete I A]

noncomputable def lift : MvPowerSeries σ 𝒪 →+* A :=
  IsAdicComplete.liftRingHom I (evalTrunc 𝒪 a I ha) (fun h => evalTrunc_compat 𝒪 a I ha h)

theorem mk_lift (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    Ideal.Quotient.mk (I ^ k) (lift 𝒪 a I ha p) =
      Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  rw [lift, IsAdicComplete.mk_liftRingHom, evalTrunc_apply]

theorem lift_coe (P : MvPolynomial σ 𝒪) :
    lift 𝒪 a I ha (P : MvPowerSeries σ 𝒪) = MvPolynomial.aeval (R := 𝒪) a P := by
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k => ?_
  rw [smodEq_pow_smul_top_iff, ← Ideal.Quotient.eq, mk_lift, Ideal.Quotient.eq, ← map_sub]
  refine idealOfVars_pow_le 𝒪 a I ha k ?_
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ hx, MvPolynomial.coeff_coe]

theorem lift_X (i : σ) : lift 𝒪 a I ha (X i) = a i := by
  rw [← MvPolynomial.coe_X, lift_coe, MvPolynomial.aeval_X]

theorem lift_C (c : 𝒪) : lift 𝒪 a I ha (C c) = algebraMap 𝒪 A c := by
  rw [← MvPolynomial.coe_C, lift_coe, MvPolynomial.aeval_C]

noncomputable def liftAlgHom : MvPowerSeries σ 𝒪 →ₐ[𝒪] A :=
  { lift 𝒪 a I ha with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, lift_C] }

theorem liftAlgHom_X (i : σ) : liftAlgHom 𝒪 a I ha (X i) = a i := lift_X 𝒪 a I ha i

end Construction

section Heads

variable {σ : Type w} {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]

theorem exists_algHom_X_eq [Finite σ] (I : Ideal A) [IsAdicComplete I A] (a : σ → A)
    (ha : ∀ i, a i ∈ I) :
    ∃ φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A, ∀ i, φ (X i) = a i :=
  ⟨liftAlgHom 𝒪 a I ha, liftAlgHom_X 𝒪 a I ha⟩

theorem algHom_ext_of_X_mem [Finite σ] (I : Ideal A) [IsHausdorff I A]
    (φ ψ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (hφ : ∀ i, φ (X i) ∈ I) (h : ∀ i, φ (X i) = ψ (X i)) :
    φ = ψ := by
  have hψ : ∀ i, ψ (X i) ∈ I := fun i => h i ▸ hφ i
  refine AlgHom.ext fun p => (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k => ?_
  rw [smodEq_pow_smul_top_iff]
  have hsplit : φ p - ψ p =
      φ (p - (truncTotal k p : MvPolynomial σ 𝒪)) - ψ (p - (truncTotal k p : MvPolynomial σ 𝒪)) := by
    rw [map_sub, map_sub, algHom_apply_coe_eq φ ψ h]; ring
  rw [hsplit]
  exact Ideal.sub_mem _
    (map_pow_span_X_le φ I hφ k (Ideal.mem_map_of_mem _ (sub_truncTotal_mem_pow_span_X k p)))
    (map_pow_span_X_le ψ I hψ k (Ideal.mem_map_of_mem _ (sub_truncTotal_mem_pow_span_X k p)))

theorem algHom_surjective_of_mk_comp_algebraMap_surjective [Finite σ] [IsLocalRing A]
    [IsNoetherianRing A] (φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (a : σ → A) (hφ : ∀ i, φ (X i) = a i)
    (ha : ∀ i, a i ∈ maximalIdeal A)
    (h𝒪 : Function.Surjective (⇑(Ideal.Quotient.mk (Ideal.span (Set.range a))) ∘ ⇑(algebraMap 𝒪 A))) :
    Function.Surjective φ := by
  classical
  set Ia : Ideal A := Ideal.span (Set.range a) with hIa
  set J : Ideal (MvPowerSeries σ 𝒪) := Ideal.span (Set.range X) with hJdef
  have hIa𝔪 : Ia ≤ maximalIdeal A := by rw [hIa, Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact ha i
  have hφ𝔪 : ∀ i, φ (X i) ∈ maximalIdeal A := fun i => (hφ i).symm ▸ ha i

  have step0 : ∀ x : A, ∃ b : MvPowerSeries σ 𝒪, x - φ b ∈ Ia := by
    intro x
    obtain ⟨c, hc⟩ := h𝒪 (Ideal.Quotient.mk Ia x)
    refine ⟨C c, ?_⟩
    rw [← Ideal.Quotient.eq, show (C c : MvPowerSeries σ 𝒪) = algebraMap 𝒪 _ c by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply], AlgHom.commutes]
    exact hc.symm

  have claim : ∀ (k : ℕ) (x : A), x ∈ Ia ^ k → ∃ b ∈ J ^ k, x - φ b ∈ Ia ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro x _
      obtain ⟨b, hb⟩ := step0 x
      exact ⟨b, by simp, by simpa using hb⟩
    | succ k ih =>
      intro x hx
      rw [pow_succ, hIa] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro m hm z hz
        induction hz using Submodule.span_induction generalizing m with
        | mem _ h =>
          obtain ⟨i, rfl⟩ := h
          obtain ⟨b, hbJ, hb⟩ := ih m hm
          refine ⟨b * X i, ?_, ?_⟩
          · rw [pow_succ]; exact Ideal.mul_mem_mul hbJ (Ideal.subset_span ⟨i, rfl⟩)
          · rw [map_mul, hφ, show m * a i - φ b * a i = (m - φ b) * a i by ring, pow_succ]
            exact Ideal.mul_mem_mul hb (Ideal.subset_span ⟨i, rfl⟩)
        | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
        | add z₁ z₂ _ _ ih₁ ih₂ =>
          obtain ⟨b₁, hb₁J, hb₁⟩ := ih₁ m hm
          obtain ⟨b₂, hb₂J, hb₂⟩ := ih₂ m hm
          refine ⟨b₁ + b₂, Ideal.add_mem _ hb₁J hb₂J, ?_⟩
          rw [show m * (z₁ + z₂) - φ (b₁ + b₂) = (m * z₁ - φ b₁) + (m * z₂ - φ b₂) by
            rw [map_add]; ring]
          exact Ideal.add_mem _ hb₁ hb₂
        | smul c z _ ihz =>
          obtain ⟨b, hbJ, hb⟩ := ihz (c * m) (Ideal.mul_mem_left _ _ hm)
          refine ⟨b, hbJ, ?_⟩
          rwa [smul_eq_mul, show m * (c * z) = c * m * z by ring]
      · intro x y hx hy
        obtain ⟨b₁, hb₁J, hb₁⟩ := hx
        obtain ⟨b₂, hb₂J, hb₂⟩ := hy
        refine ⟨b₁ + b₂, Ideal.add_mem _ hb₁J hb₂J, ?_⟩
        rw [show x + y - φ (b₁ + b₂) = (x - φ b₁) + (y - φ b₂) by rw [map_add]; ring]
        exact Ideal.add_mem _ hb₁ hb₂
  choose β hβJ hβ using claim
  intro x

  let t : (k : ℕ) → {s : MvPowerSeries σ 𝒪 // x - φ s ∈ Ia ^ k} :=
    fun k => Nat.rec ⟨0, by simp⟩
      (fun k sk => ⟨sk.1 + β k (x - φ sk.1) sk.2, by
        rw [map_add, show x - (φ sk.1 + φ (β k (x - φ sk.1) sk.2)) =
          (x - φ sk.1) - φ (β k (x - φ sk.1) sk.2) by ring]
        exact hβ k _ sk.2⟩) k
  let s : ℕ → MvPowerSeries σ 𝒪 := fun k => (t k).1
  have hs_succ : ∀ k, s (k + 1) = s k + β k (x - φ (s k)) (t k).2 := fun k => rfl
  have hsI : ∀ k, x - φ (s k) ∈ Ia ^ k := fun k => (t k).2
  have hcauchy : ∀ m l, m ≤ l → s l - s m ∈ J ^ m := by
    intro m l hml
    induction l, hml using Nat.le_induction with
    | base => simp
    | succ k hmk ihk =>
      rw [hs_succ, show s k + β k (x - φ (s k)) (t k).2 - s m =
        (s k - s m) + β k (x - φ (s k)) (t k).2 by ring]
      exact Ideal.add_mem _ ihk (Ideal.pow_le_pow_right hmk (hβJ k _ (t k).2))

  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete J (MvPowerSeries σ 𝒪))
    (f := s) (fun {m l} hml => by
      rw [smodEq_pow_smul_top_iff]
      have := hcauchy m l hml
      rwa [← neg_sub, Ideal.neg_mem_iff])
  refine ⟨L, ?_⟩
  refine (IsHausdorff.eq_iff_smodEq (I := maximalIdeal A)).mpr fun k => ?_
  rw [smodEq_pow_smul_top_iff, show φ L - x = φ (L - s k) - (x - φ (s k)) by rw [map_sub]; ring]
  refine Ideal.sub_mem _ ?_ (Ideal.pow_right_mono hIa𝔪 k (hsI k))
  refine map_pow_span_X_le φ _ hφ𝔪 k (Ideal.mem_map_of_mem _ ?_)
  have := (smodEq_pow_smul_top_iff J k _ _).mp (hL k)
  rwa [← neg_sub, Ideal.neg_mem_iff] at this

theorem exists_mvPowerSeries_algHom_surjective [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (hres : Function.Surjective (⇑(residue A) ∘ ⇑(algebraMap 𝒪 A))) :
    ∃ (n : ℕ) (φ : MvPowerSeries (Fin n) 𝒪 →ₐ[𝒪] A), Function.Surjective φ := by
  obtain ⟨n, a, hspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (maximalIdeal A))
  have ha : ∀ i, a i ∈ maximalIdeal A := fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_algHom_X_eq (𝒪 := 𝒪) (maximalIdeal A) a ha
  refine ⟨n, φ, algHom_surjective_of_mk_comp_algebraMap_surjective φ a hφ ha fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := hres (residue A x)
  refine ⟨c, ?_⟩
  simp only [Function.comp_apply] at hc ⊢
  rw [Ideal.Quotient.eq]
  have : algebraMap 𝒪 A c - x ∈ maximalIdeal A := by
    rw [← Ideal.Quotient.eq]; exact hc
  change algebraMap 𝒪 A c - x ∈ Ideal.span (Set.range a)
  rw [← Ideal.submodule_span_eq, hspan]
  exact this

end Heads

end M4cP4PS

theorem solution {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ]
    [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A) [IsHausdorff I A]
    (φ ψ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ I)
    (h : ∀ i, φ (MvPowerSeries.X i) = ψ (MvPowerSeries.X i)) : φ = ψ :=
  M4cP4PS.algHom_ext_of_X_mem I φ ψ hφ h

end S_MvPowerSeries_algHom_ext_of_apply_X_mem
end P2MW
export P2MW.S_MvPowerSeries_algHom_ext_of_apply_X_mem (solution)
