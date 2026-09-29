-- Prove2me | solution 1 for Module.exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/dd12c161-bc73-56aa-93be-bb01736edbf2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq

set_option autoImplicit false

universe u v

open TensorProduct

namespace EXREF

variable {A : Type u} [CommRing A]

theorem exists_crt_coeff (S : Finset (Ideal A)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsMaximal) (𝔭 : Ideal A) (h𝔭 : 𝔭 ∈ S) :
    ∃ a : A, a - 1 ∈ 𝔭 ∧ ∀ 𝔮 ∈ S, 𝔮 ≠ 𝔭 → a ∈ 𝔮 := by
  classical
  have htop : 𝔭 ⊔ ⨅ 𝔮 ∈ S.erase 𝔭, 𝔮 = ⊤ := by
    refine Ideal.sup_iInf_eq_top ?_
    intro 𝔮 h𝔮
    obtain ⟨hne, h𝔮S⟩ := Finset.mem_erase.mp h𝔮
    exact (hS 𝔭 h𝔭).coprime_of_ne (hS 𝔮 h𝔮S) (Ne.symm hne)
  have h1 : (1 : A) ∈ 𝔭 ⊔ ⨅ 𝔮 ∈ S.erase 𝔭, 𝔮 := by rw [htop]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  refine ⟨y, ?_, fun 𝔮 h𝔮 hne => ?_⟩
  · have : y - 1 = -x := by rw [← hxy]; ring
    rw [this]; exact 𝔭.neg_mem hx
  · have hy' := (Submodule.mem_iInf _).mp hy 𝔮
    exact (Submodule.mem_iInf _).mp hy' (Finset.mem_erase.mpr ⟨hne, h𝔮⟩)

variable {P : Type v} [AddCommGroup P] [Module A P]

theorem exists_lift_basis_fibre (𝔭 : Ideal A) [𝔭.IsMaximal] [Module.Finite A P] (d : ℕ)
    (hrank : Module.finrank (A ⧸ 𝔭) ((A ⧸ 𝔭) ⊗[A] P) = d) :
    ∃ (e : Fin d → P) (b : Module.Basis (Fin d) (A ⧸ 𝔭) ((A ⧸ 𝔭) ⊗[A] P)),
      ∀ i, b i = (1 : A ⧸ 𝔭) ⊗ₜ[A] e i := by
  letI : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  let b : Module.Basis (Fin d) (A ⧸ 𝔭) ((A ⧸ 𝔭) ⊗[A] P) := Module.finBasisOfFinrankEq _ _ hrank
  have hsurj : Function.Surjective (TensorProduct.mk A (A ⧸ 𝔭) P 1) :=
    TensorProduct.mk_surjective A P (A ⧸ 𝔭) Ideal.Quotient.mk_surjective
  choose e he using fun i => hsurj (b i)
  exact ⟨e, b, fun i => (he i).symm⟩

theorem mem_smul_top_of_tmul_eq_zero (𝔮 : Ideal A) (p : P) (h : (1 : A ⧸ 𝔮) ⊗ₜ[A] p = 0) :
    p ∈ 𝔮 • (⊤ : Submodule A P) := by
  have h2 : TensorProduct.quotTensorEquivQuotSMul P 𝔮 (Ideal.Quotient.mk 𝔮 1 ⊗ₜ[A] p) = 0 := by
    rw [map_one, h, map_zero]
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul] at h2
  exact (Submodule.Quotient.mk_eq_zero _).mp h2

theorem smul_one_tmul (𝔮 : Ideal A) (a : A) (p : P) :
    a • ((1 : A ⧸ 𝔮) ⊗ₜ[A] p) = (Ideal.Quotient.mk 𝔮 a) • ((1 : A ⧸ 𝔮) ⊗ₜ[A] p) := by
  rw [← IsScalarTower.algebraMap_smul (A ⧸ 𝔮) a, Ideal.Quotient.algebraMap_eq]

theorem exists_forall_not_mem_and_linearIndependent_and_smul_mem_span
    [IsDomain A] [Module.Finite A P] (d : ℕ)
    (S : Finset (Ideal A)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsMaximal) (hSne : S.Nonempty)
    (hrank : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (K ⊗[A] P) = d) :
    ∃ (f : A) (e : Fin d → P), (∀ 𝔭 ∈ S, f ∉ 𝔭) ∧
      (∀ c : Fin d → A, ∑ i, c i • e i = 0 → c = 0) ∧
      (∀ p : P, ∃ c : Fin d → A, f • p = ∑ i, c i • e i) := by
  classical

  have hb : ∀ 𝔭 : S, ∃ (e : Fin d → P)
      (b : Module.Basis (Fin d) (A ⧸ (𝔭 : Ideal A)) ((A ⧸ (𝔭 : Ideal A)) ⊗[A] P)),
      ∀ i, b i = (1 : A ⧸ (𝔭 : Ideal A)) ⊗ₜ[A] e i := fun 𝔭 => by
    haveI := hS 𝔭 𝔭.2
    letI : Field (A ⧸ (𝔭 : Ideal A)) := Ideal.Quotient.field _
    exact exists_lift_basis_fibre (𝔭 : Ideal A) d (hrank (A ⧸ (𝔭 : Ideal A)))
  choose eloc b hb using hb
  have ha : ∀ 𝔭 : S, ∃ a : A, a - 1 ∈ (𝔭 : Ideal A) ∧ ∀ 𝔮 ∈ S, 𝔮 ≠ 𝔭 → a ∈ 𝔮 := fun 𝔭 =>
    exists_crt_coeff S hS 𝔭 𝔭.2
  choose a ha1 ha0 using ha

  let e : Fin d → P := fun i => ∑ 𝔭 : S, a 𝔭 • eloc 𝔭 i
  have he_fibre : ∀ (𝔮 : S) (i : Fin d), (1 : A ⧸ (𝔮 : Ideal A)) ⊗ₜ[A] e i = b 𝔮 i := by
    intro 𝔮 i
    simp only [e, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    rw [Finset.sum_eq_single_of_mem 𝔮 (Finset.mem_univ _)]
    · rw [smul_one_tmul, hb 𝔮 i]
      have h1 : Ideal.Quotient.mk (𝔮 : Ideal A) (a 𝔮) = 1 := by
        rw [← (Ideal.Quotient.mk (𝔮 : Ideal A)).map_one, Ideal.Quotient.eq]
        exact ha1 𝔮
      rw [h1, one_smul]
    · intro 𝔭 _ hne
      have hmem : a 𝔭 ∈ (𝔮 : Ideal A) := ha0 𝔭 𝔮 𝔮.2 (fun h => hne (Subtype.ext h).symm)
      rw [smul_one_tmul, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_smul]

  let φ : (Fin d → A) →ₗ[A] P := Fintype.linearCombination A e
  have hφ : ∀ c, φ c = ∑ i, c i • e i := fun c => by simp [φ, Fintype.linearCombination_apply]
  have hkill : ∀ 𝔮 : S, ∃ r : A, r - 1 ∈ (𝔮 : Ideal A) ∧ ∀ p : P, r • p ∈ LinearMap.range φ := by
    intro 𝔮

    have hsup : ∀ p : P, p ∈ LinearMap.range φ ⊔ (𝔮 : Ideal A) • (⊤ : Submodule A P) := by
      intro p

      choose c hc using fun i => Ideal.Quotient.mk_surjective ((b 𝔮).repr ((1 : A ⧸ (𝔮 : Ideal A)) ⊗ₜ[A] p) i)
      have hsum : (1 : A ⧸ (𝔮 : Ideal A)) ⊗ₜ[A] (∑ i, c i • e i) = (1 : A ⧸ (𝔮 : Ideal A)) ⊗ₜ[A] p := by
        rw [TensorProduct.tmul_sum]
        conv_rhs => rw [← (b 𝔮).sum_repr ((1 : A ⧸ (𝔮 : Ideal A)) ⊗ₜ[A] p)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.tmul_smul, smul_one_tmul, hc i, he_fibre 𝔮 i]
      have hdiff : (1 : A ⧸ (𝔮 : Ideal A)) ⊗ₜ[A] (p - ∑ i, c i • e i) = 0 := by
        rw [TensorProduct.tmul_sub, hsum, sub_self]
      have hker := mem_smul_top_of_tmul_eq_zero (𝔮 : Ideal A) _ hdiff
      refine Submodule.mem_sup.mpr ⟨∑ i, c i • e i, ⟨c, hφ c⟩, p - ∑ i, c i • e i, hker, ?_⟩
      abel

    have hM : (⊤ : Submodule A (P ⧸ LinearMap.range φ)) ≤ (𝔮 : Ideal A) • ⊤ := by
      rintro x -
      obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φ) x
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hsup p)
      rw [← hyz, map_add]
      simp only [Submodule.mkQ_apply]
      rw [(Submodule.Quotient.mk_eq_zero (LinearMap.range φ)).mpr hy, zero_add]

      refine Submodule.smul_induction_on hz (fun t ht n _ => ?_) (fun x y hx hy => ?_)
      · rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem_smul ht Submodule.mem_top
      · rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hx hy
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (𝔮 : Ideal A)
      (⊤ : Submodule A (P ⧸ LinearMap.range φ)) Module.Finite.fg_top hM
    refine ⟨r, hr1, fun p => ?_⟩
    have h0 := hr (Submodule.Quotient.mk p) Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  choose r hr1 hr using hkill

  let J : Ideal A := Module.annihilator A (P ⧸ LinearMap.range φ)
  have hrJ : ∀ 𝔮 : S, r 𝔮 ∈ J := by
    intro 𝔮
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φ) x
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hr 𝔮 p
  have hJ : ¬ ((J : Set A) ⊆ ⋃ 𝔮 ∈ (↑S : Set (Ideal A)), (𝔮 : Set A)) := by
    obtain ⟨𝔭₀, h𝔭₀⟩ := hSne
    rw [Ideal.subset_union_prime 𝔭₀ 𝔭₀ (fun 𝔮 h𝔮 _ _ => (hS 𝔮 h𝔮).isPrime)]
    rintro ⟨𝔮, h𝔮, hle⟩
    have h1 : r ⟨𝔮, h𝔮⟩ ∈ 𝔮 := hle (hrJ ⟨𝔮, h𝔮⟩)
    have h2 : (1 : A) ∈ 𝔮 := by
      have := 𝔮.sub_mem h1 (hr1 ⟨𝔮, h𝔮⟩)
      rwa [sub_sub_cancel] at this
    exact (hS 𝔮 h𝔮).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨f, hfJ, hfS⟩ := Set.not_subset.mp hJ
  have hfS' : ∀ 𝔭 ∈ S, f ∉ 𝔭 := by
    intro 𝔭 h𝔭 hf
    exact hfS (Set.mem_iUnion₂.mpr ⟨𝔭, Finset.mem_coe.mpr h𝔭, hf⟩)
  have hf_range : ∀ p : P, f • p ∈ LinearMap.range φ := by
    intro p
    have h0 := Module.mem_annihilator.mp hfJ (Submodule.Quotient.mk p)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    exact h0

  have hf0 : f ≠ 0 := by
    obtain ⟨𝔭₀, h𝔭₀⟩ := hSne
    intro h; exact hfS' 𝔭₀ h𝔭₀ (h ▸ 𝔭₀.zero_mem)
  let K := FractionRing A
  have hinj : ∀ c : Fin d → A, φ c = 0 → c = 0 := by
    intro c hc

    let φK : (Fin d → K) →ₗ[K] K ⊗[A] P := Fintype.linearCombination K (fun i => (1 : K) ⊗ₜ[A] e i)
    have hφK : ∀ c' : Fin d → K, φK c' = ∑ i, c' i • ((1 : K) ⊗ₜ[A] e i) := fun c' => by
      simp [φK, Fintype.linearCombination_apply]

    have hsurjK : Function.Surjective φK := by
      have hgen : ∀ p : P, (1 : K) ⊗ₜ[A] p ∈ LinearMap.range φK := by
        intro p
        obtain ⟨c', hc'⟩ := LinearMap.mem_range.mp (hf_range p)
        have hfu : IsUnit (algebraMap A K f) := IsUnit.mk0 _ (by
          rwa [Ne, IsFractionRing.to_map_eq_zero_iff])
        refine ⟨fun i => hfu.unit⁻¹.1 * algebraMap A K (c' i), ?_⟩
        rw [hφK]
        simp_rw [mul_smul, ← Finset.smul_sum, IsScalarTower.algebraMap_smul, ← TensorProduct.tmul_smul,
          ← TensorProduct.tmul_sum, ← hφ c', hc', TensorProduct.tmul_smul]
        rw [← IsScalarTower.algebraMap_smul K f, smul_smul, IsUnit.val_inv_mul, one_smul]
      intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul k p =>
        obtain ⟨c', hc'⟩ := hgen p
        refine ⟨k • c', ?_⟩
        rw [map_smul, hc', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy =>
        obtain ⟨cx, hcx⟩ := hx; obtain ⟨cy, hcy⟩ := hy
        exact ⟨cx + cy, by rw [map_add, hcx, hcy]⟩

    haveI : Module.Finite K (K ⊗[A] P) := Module.Finite.base_change A K P
    have hinjK : Function.Injective φK := by
      have hdim : Module.finrank K (Fin d → K) = Module.finrank K (K ⊗[A] P) := by
        rw [Module.finrank_fin_fun, hrank K]
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurjK

    have himg : φK (fun i => algebraMap A K (c i)) = 0 := by
      rw [hφK]
      simp_rw [IsScalarTower.algebraMap_smul, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_sum, ← hφ c, hc,
        TensorProduct.tmul_zero]
    have hzero : (fun i => algebraMap A K (c i)) = 0 := hinjK (by rw [himg, map_zero])
    funext i
    have := congr_fun hzero i
    exact (IsFractionRing.injective A K) (by simpa using this)
  exact ⟨f, e, hfS', fun c hc => hinj c (by rw [hφ]; exact hc), fun p => by
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp (hf_range p)
    exact ⟨c, by rw [← hc, hφ]⟩⟩

end EXREF

theorem solution
    {A : Type u} [CommRing A] [IsDomain A] {P : Type v} [AddCommGroup P] [Module A P] [Module.Finite A P]
    (d : ℕ) (S : Finset (Ideal A)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsMaximal) (hSne : S.Nonempty)
    (hrank : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = d) :
    ∃ (f : A) (e : Fin d → P), (∀ 𝔭 ∈ S, f ∉ 𝔭) ∧ LinearIndependent A e ∧
      ∀ p : P, f • p ∈ Submodule.span A (Set.range e) := by
  obtain ⟨f, e, hf, hind, hspan⟩ :=
    EXREF.exists_forall_not_mem_and_linearIndependent_and_smul_mem_span (A := A) (P := P) d S hS hSne hrank
  refine ⟨f, e, hf, Fintype.linearIndependent_iff.mpr (fun c hc i => congr_fun (hind c hc) i), fun p => ?_⟩
  obtain ⟨c, hc⟩ := hspan p
  rw [hc]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

end S_Module_exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq
end P2MW
export P2MW.S_Module_exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq (solution)
