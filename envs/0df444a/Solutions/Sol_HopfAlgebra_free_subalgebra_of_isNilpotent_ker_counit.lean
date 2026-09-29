-- Prove2me | solution 1 for HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7324163e-a061-5a98-9c99-4470bc6c5fc0

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

universe u v

namespace S17Nil

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H)

abbrev augK : Ideal ↥K := RingHom.ker ((Bialgebra.counitAlgHom k H).comp K.val)

abbrev JH : Ideal H := Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}

theorem mem_augK_iff (x : ↥K) : x ∈ augK K ↔ Coalgebra.counit (R := k) (x : H) = 0 := by
  rw [RingHom.mem_ker]; rfl

theorem JH_eq_map : JH K = Ideal.map (algebraMap ↥K H) (augK K) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x ⟨hxK, hx⟩
    exact Ideal.mem_map_of_mem (algebraMap ↥K H) ((mem_augK_iff K ⟨x, hxK⟩).mpr hx)
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact Ideal.subset_span ⟨x.2, (mem_augK_iff K x).mp hx⟩

theorem restrictScalars_JH : (JH K).restrictScalars ↥K = augK K • (⊤ : Submodule ↥K H) := by
  rw [Ideal.smul_top_eq_map, ← JH_eq_map]

theorem JH_pow_eq_bot (hnil : IsNilpotent (augK K)) : ∃ n : ℕ, JH K ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  rw [JH_eq_map, ← Ideal.map_pow, hn, Submodule.zero_eq_bot, Ideal.map_bot]

theorem mk_coe_eq (x : ↥K) :
    Ideal.Quotient.mk (JH K) (x : H) = algebraMap k (H ⧸ JH K) (Coalgebra.counit (R := k) (x : H)) := by
  rw [IsScalarTower.algebraMap_apply k H (H ⧸ JH K), Ideal.Quotient.algebraMap_eq, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.subset_span ⟨?_, ?_⟩
  · exact Subalgebra.sub_mem _ x.2 (Subalgebra.algebraMap_mem _ _)
  · rw [map_sub, Bialgebra.counit_algebraMap, sub_self]

theorem coe_smul_quot (x : ↥K) (q : H ⧸ JH K) : x • q = Coalgebra.counit (R := k) (x : H) • q := by
  rw [Algebra.smul_def, Algebra.smul_def]
  congr 1
  exact mk_coe_eq K x

theorem eq_top_of_le_sup_smul {I : Ideal ↥K} (hI : IsNilpotent I) (N : Submodule ↥K H)
    (h : (⊤ : Submodule ↥K H) ≤ N ⊔ I • ⊤) : N = ⊤ := by
  have key : ∀ m : ℕ, (⊤ : Submodule ↥K H) ≤ N ⊔ I ^ m • ⊤ := by
    intro m
    induction m with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
    | succ m ih =>
        have h1 : I • (⊤ : Submodule ↥K H) ≤ N ⊔ I ^ (m + 1) • ⊤ := by
          calc I • (⊤ : Submodule ↥K H) ≤ I • (N ⊔ I ^ m • ⊤) := Submodule.smul_mono le_rfl ih
            _ = I • N ⊔ I ^ (m + 1) • ⊤ := by rw [Submodule.smul_sup, ← Submodule.mul_smul, pow_succ']
            _ ≤ N ⊔ I ^ (m + 1) • ⊤ := sup_le_sup_right Submodule.smul_le_right _
        exact h.trans (sup_le le_sup_left h1)
  obtain ⟨n, hn⟩ := hI
  have := key n
  rw [hn, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact eq_top_iff.mpr this

section Core

variable {ι : Type*} (e : ι → H)

noncomputable abbrev Λ : (ι →₀ ↥K) →ₗ[↥K] H := Finsupp.linearCombination ↥K e

theorem range_Λ_eq_top (hnil : IsNilpotent (augK K)) (b : Module.Basis ι k (H ⧸ JH K))
    (he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i) : LinearMap.range (Λ K e) = ⊤ := by
  classical
  apply eq_top_of_le_sup_smul K hnil
  rintro h -
  let q : H →ₐ[k] H ⧸ JH K := Ideal.Quotient.mkₐ k (JH K)
  have hq : ∀ y, q y = Ideal.Quotient.mk (JH K) y := fun _ => rfl
  set c := b.repr (q h) with hc
  set h₀ : H := c.sum fun i a => a • e i with hh₀
  have hq₀ : q h₀ = q h := by
    rw [hh₀, map_finsuppSum]
    conv_rhs => rw [← b.linearCombination_repr (q h), Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [map_smul, hq, he]
  have hdiff : h - h₀ ∈ (JH K).restrictScalars ↥K := by
    show h - h₀ ∈ JH K
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hq, map_sub, hq₀, sub_self]
  have hh₀N : h₀ ∈ LinearMap.range (Λ K e) := by
    refine ⟨c.mapRange (algebraMap k ↥K) (map_zero _), ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
    · rw [hh₀]; exact Finsupp.sum_congr fun i _ => algebraMap_smul (↥K) (c i) (e i)
    · intro i; exact zero_smul _ _
  rw [restrictScalars_JH] at hdiff
  have : h = h₀ + (h - h₀) := by ring
  rw [this]
  exact Submodule.add_mem_sup hh₀N hdiff

noncomputable abbrev Λ' : (ι →₀ H) →ₗ[H] (H ⊗[↥K] H) :=
  Finsupp.linearCombination H (fun i => (1 : H) ⊗ₜ[↥K] e i)

theorem Λ'_surjective (hΛ : LinearMap.range (Λ K e) = ⊤) : Function.Surjective (Λ' K e) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro z -
  induction z with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul h h' =>
      have hh' : h' ∈ LinearMap.range (Λ K e) := by rw [hΛ]; exact Submodule.mem_top
      obtain ⟨a, rfl⟩ := hh'
      have : h ⊗ₜ[↥K] (Λ K e a) = h • ((1 : H) ⊗ₜ[↥K] (Λ K e a)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      refine Submodule.smul_mem _ h ?_
      rw [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← TensorProduct.smul_tmul]

      have : ((a i) • (1 : H)) ⊗ₜ[↥K] e i = (algebraMap ↥K H (a i)) • ((1 : H) ⊗ₜ[↥K] e i) := by
        rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (LinearMap.mem_range.mpr ⟨Finsupp.single i 1, by simp [Finsupp.linearCombination_single]⟩)

theorem mk_smul (x : ↥K) (h : H) :
    Ideal.Quotient.mk (JH K) (x • h) = Coalgebra.counit (R := k) (x : H) • Ideal.Quotient.mk (JH K) h := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  exact mk_coe_eq K x

noncomputable def θ : H ⊗[↥K] H →ₗ[↥K] (H ⧸ JH K) ⊗[k] (H ⧸ JH K) :=
  TensorProduct.lift
    (LinearMap.mk₂ ↥K (fun h h' => Ideal.Quotient.mk (JH K) h ⊗ₜ[k] Ideal.Quotient.mk (JH K) h')
      (fun h₁ h₂ h' => by simp only [map_add, TensorProduct.add_tmul])
      (fun x h h' => by
        rw [mk_smul, ← coe_smul_quot]
        exact (TensorProduct.smul_tmul' x _ _).symm)
      (fun h h₁ h₂ => by simp only [map_add, TensorProduct.tmul_add])
      (fun x h h' => by
        rw [mk_smul, TensorProduct.tmul_smul]
        refine ((TensorProduct.smul_tmul' x _ _).trans ?_).symm
        rw [coe_smul_quot, TensorProduct.smul_tmul']))

theorem θ_tmul (h h' : H) :
    θ K (h ⊗ₜ[↥K] h') = Ideal.Quotient.mk (JH K) h ⊗ₜ[k] Ideal.Quotient.mk (JH K) h' :=
  TensorProduct.lift.tmul _ _

theorem apply_mem_JH_of_Λ'_eq_zero (b : Module.Basis ι k (H ⧸ JH K))
    (he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i) (m : ι →₀ H) (hm : Λ' K e m = 0) (i : ι) :
    m i ∈ JH K := by
  classical

  let Φ : (H ⧸ JH K) ⊗[k] (H ⧸ JH K) ≃ₗ[k] (ι →₀ H ⧸ JH K) :=
    (TensorProduct.congr (LinearEquiv.refl k _) b.repr).trans (TensorProduct.finsuppScalarRight k k (H ⧸ JH K) ι)
  have hΦ : ∀ (q : H ⧸ JH K) (j : ι), Φ (q ⊗ₜ[k] b j) = Finsupp.single j q := by
    intro q j
    simp [Φ, TensorProduct.finsuppScalarRight_apply_tmul, Finsupp.sum_single_index]
  have hcalc : Φ (θ K (Λ' K e m)) = m.mapRange (Ideal.Quotient.mk (JH K)) (map_zero _) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum]
    have : ∀ j ∈ m.support, Φ (θ K (m j • ((1 : H) ⊗ₜ[↥K] e j))) = Finsupp.single j (Ideal.Quotient.mk (JH K) (m j)) := by
      intro j _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, θ_tmul, he, hΦ]
    rw [Finset.sum_congr rfl this]
    ext j
    rw [Finset.sum_apply', Finsupp.mapRange_apply]
    rw [Finset.sum_eq_single j]
    · rw [Finsupp.single_eq_same]
    · intro j' _ hj'; rw [Finsupp.single_apply, if_neg hj']
    · intro hj; rw [Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hj, map_zero]
  rw [hm, map_zero, map_zero] at hcalc
  have := DFunLike.congr_fun hcalc.symm i
  rw [Finsupp.mapRange_apply, Finsupp.zero_apply] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

theorem ker_Λ'_eq_bot
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hnil : IsNilpotent (augK K)) (b : Module.Basis ι k (H ⧸ JH K))
    (he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i) : LinearMap.ker (Λ' K e) = ⊥ := by
  classical

  obtain ⟨β, -⟩ := HopfAlgebra.exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span K hΔ
  haveI : Module.Free H (H ⊗[k] (H ⧸ JH K)) := Module.Free.of_basis (Algebra.TensorProduct.basis H b)
  haveI : Module.Projective H (H ⊗[↥K] H) := Module.Projective.of_equiv β.toLinearEquiv.symm

  have hsurj : Function.Surjective (Λ' K e) := Λ'_surjective K e (range_Λ_eq_top K e hnil b he)
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (Λ' K e) LinearMap.id hsurj
  set M := LinearMap.ker (Λ' K e) with hM

  let p : (ι →₀ H) →ₗ[H] (ι →₀ H) := LinearMap.id - σ ∘ₗ (Λ' K e)
  have hp_mem : ∀ v, p v ∈ M := by
    intro v
    rw [hM, LinearMap.mem_ker]
    show Λ' K e (v - σ (Λ' K e v)) = 0
    rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
  have hp_fix : ∀ v ∈ M, p v = v := by
    intro v hv
    show v - σ (Λ' K e v) = v
    rw [LinearMap.mem_ker.mp hv, map_zero, sub_zero]

  have hMJ : M ≤ (JH K) • M := by
    intro v hv
    have hvJ : v ∈ (JH K) • (⊤ : Submodule H (ι →₀ H)) := by
      have hv' : v = v.sum fun i a => a • Finsupp.single i (1 : H) := by
        conv_lhs => rw [← Finsupp.sum_single v]
        exact Finsupp.sum_congr fun i _ => by rw [Finsupp.smul_single_one]
      rw [hv']
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      exact apply_mem_JH_of_Λ'_eq_zero K e b he v (LinearMap.mem_ker.mp hv) i
    have h1 : p v ∈ Submodule.map p ((JH K) • ⊤) := Submodule.mem_map_of_mem hvJ
    rw [Submodule.map_smul'', hp_fix v hv] at h1
    refine Submodule.smul_mono le_rfl ?_ h1
    rintro _ ⟨w, -, rfl⟩
    exact hp_mem w

  have hiter : ∀ j : ℕ, M ≤ (JH K) ^ j • M := by
    intro j
    induction j with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ j ih =>
        calc M ≤ (JH K) ^ j • M := ih
          _ ≤ (JH K) ^ j • ((JH K) • M) := Submodule.smul_mono le_rfl hMJ
          _ = (JH K) ^ (j + 1) • M := by rw [← Submodule.mul_smul, ← pow_succ]
  obtain ⟨n, hn⟩ := JH_pow_eq_bot K hnil
  have := hiter n
  rw [hn, Submodule.bot_smul] at this
  exact le_bot_iff.mp this

theorem Λ_injective
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hnil : IsNilpotent (augK K)) (b : Module.Basis ι k (H ⧸ JH K))
    (he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i) : Function.Injective (Λ K e) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  let a' : ι →₀ H := a.mapRange (algebraMap ↥K H) (map_zero _)
  have ha' : Λ' K e a' = (1 : H) ⊗ₜ[↥K] Λ K e a := by
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
    · rw [Finsupp.sum, Finsupp.sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul]
    · intro i; exact zero_smul _ _
  have hker : a' ∈ LinearMap.ker (Λ' K e) := by
    rw [LinearMap.mem_ker, ha', ha, TensorProduct.tmul_zero]
  rw [ker_Λ'_eq_bot K e hΔ hnil b he, Submodule.mem_bot] at hker
  ext i
  have := DFunLike.congr_fun hker i
  rw [Finsupp.mapRange_apply, Finsupp.zero_apply] at this
  simpa using this

end Core

end S17Nil

open S17Nil in
theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (hnil : IsNilpotent (RingHom.ker ((Bialgebra.counitAlgHom k H).comp K.val))) :
    Module.Free ↥K H := by
  classical
  let b := Module.Free.chooseBasis k (H ⧸ JH K)
  have hsurj := Ideal.Quotient.mk_surjective (I := JH K)
  let e : Module.Free.ChooseBasisIndex k (H ⧸ JH K) → H := fun i => (hsurj (b i)).choose
  have he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i := fun i => (hsurj (b i)).choose_spec
  have hbij : Function.Bijective (Λ K e) :=
    ⟨Λ_injective K e hΔ hnil b he, LinearMap.range_eq_top.mp (range_Λ_eq_top K e hnil b he)⟩
  exact Module.Free.of_equiv (LinearEquiv.ofBijective (Λ K e) hbij)

end S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit
end P2MW
export P2MW.S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit (solution)
