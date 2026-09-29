-- Prove2me | solution 1 for HopfAlgebra.finiteType_hopfKer_of_finitePartIdempotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ca91b3fd-09ba-5717-bbb5-7db4263377e2

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finiteType_hopfKer_of_finitePartIdempotent

set_option autoImplicit false

open scoped TensorProduct

namespace S17S52

theorem one_tmul_injective (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Function.Injective (fun m : M => (1 : K) ⊗ₜ[R] m) := by
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hfact : (fun m : M => (1 : K) ⊗ₜ[R] m) =
      (LinearMap.rTensor M (Algebra.linearMap R K)) ∘ (TensorProduct.lid R M).symm := by
    ext m; simp [TensorProduct.lid_symm_apply, Algebra.linearMap_apply]
  rw [hfact]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ hRK).comp
    (TensorProduct.lid R M).symm.injective

theorem exists_eq_unit_mul_pow_generator (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) (s : R) (hs : s ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ), s = u * π ^ n := by
  by_cases hfield : IsField R
  ·
    obtain ⟨t, ht⟩ := hfield.mul_inv_cancel hs
    exact ⟨0, Units.mkOfMulEqOne s t ht, by simp⟩
  ·
    haveI : IsDiscreteValuationRing R := by
      refine (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mpr ⟨inferInstance, ?_⟩
      refine ⟨IsLocalRing.maximalIdeal R, ⟨?_, inferInstance⟩, ?_⟩
      · intro h0
        apply hfield
        exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr h0
      · rintro Q ⟨hQ0, hQ⟩
        haveI := hQ
        exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hQ0)
    have hirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hirr
    exact ⟨n, u, rfl⟩

theorem exists_finset_span_mul_orbit
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Flat R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H')
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0) :
    ∃ S : Finset H, (↑S : Set H) ⊆ HopfAlgebra.hopfKer qc ∧
      ∀ b ∈ HopfAlgebra.hopfKer qc, b * f ∈ Submodule.span R (↑S : Set H) := by
  classical
  set B := HopfAlgebra.hopfKer qc with hB
  let Lₑ := Localization.Away e
  let ι : H →ₐ[R] Lₑ := IsScalarTower.toAlgHom R H Lₑ

  let Ψ : H →ₗ[R] Lₑ := ι.toLinearMap ∘ₗ LinearMap.mulRight R e
  have hΨ : ∀ b : H, Ψ b = algebraMap H Lₑ (b * e) := fun _ => rfl

  have hΨ0 : ∀ z : H, Ψ z = 0 → z * e = 0 := by
    intro z hz
    rw [hΨ] at hz
    obtain ⟨⟨m, k, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers e) Lₑ (z * e)).mp hz
    simp only at hm
    cases k with
    | zero => simpa using hm
    | succ k =>
        have hek : e ^ (k + 1) = e := he.pow_succ_eq k
        rw [hek] at hm
        calc z * e = z * (e * e) := by rw [he.eq]
          _ = e * (z * e) := by ring
          _ = 0 := hm

  haveI : IsNoetherian R Lₑ := isNoetherian_of_isNoetherianRing_of_finite R Lₑ
  let N : Submodule R Lₑ := Submodule.map Ψ (Subalgebra.toSubmodule B)
  obtain ⟨G, hG⟩ : N.FG := IsNoetherian.noetherian N

  have hpre : ∀ g : Lₑ, g ∈ G → ∃ b : H, b ∈ B ∧ Ψ b = g := by
    intro g hg
    have : g ∈ N := by rw [← hG]; exact Submodule.subset_span hg
    obtain ⟨b, hb, hbg⟩ := Submodule.mem_map.mp this
    exact ⟨b, hb, hbg⟩
  choose! pre hpreB hpreΨ using hpre
  refine ⟨G.image (fun g => pre g * f), ?_, ?_⟩
  · intro y hy
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hy)
    exact Subalgebra.mul_mem _ (hpreB g hg) hfK
  · intro b hb
    have hbN : Ψ b ∈ Submodule.span R (↑G : Set Lₑ) := by
      rw [hG]; exact Submodule.mem_map_of_mem hb
    obtain ⟨r, -, hr⟩ := Submodule.mem_span_finset.mp hbN

    set d := b - ∑ g ∈ G, r g • pre g with hd
    have hΨd : Ψ d = 0 := by
      rw [hd, map_sub, map_sum, sub_eq_zero, ← hr]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_smul, hpreΨ g hg]
    have hdB : d ∈ B := by
      rw [hd]
      refine Subalgebra.sub_mem _ hb (Subalgebra.sum_mem _ fun g hg => Subalgebra.smul_mem _ (hpreB g hg) _)
    have hdf : d * f = 0 := hmin d hdB (hΨ0 d hΨd)
    have hbf : b * f = ∑ g ∈ G, r g • (pre g * f) := by
      have : b = d + ∑ g ∈ G, r g • pre g := by rw [hd]; ring
      rw [this, add_mul, hdf, zero_add, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [smul_mul_assoc]
    rw [hbf]
    refine Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨g, hg, rfl⟩)

theorem exists_inv_uniformizer_mem_and_finset
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Flat R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H')
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0) :
    ∃ x ∈ HopfAlgebra.hopfKer qc, ∃ T : Finset H, (↑T : Set H) ⊆ HopfAlgebra.hopfKer qc ∧
      ∀ b ∈ HopfAlgebra.hopfKer qc, ∃ n : ℕ, ∃ c ∈ Submodule.span R (↑T : Set H), b * (1 - f) = x ^ n * c := by
  classical
  set B := HopfAlgebra.hopfKer qc with hB

  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal R)).principal
  have hπ' : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπ

  have h1e : IsIdempotentElem (1 - e) := he.one_sub
  have hpow : ∀ i : ℕ, (1 - e) ^ i * (1 - e) = (1 - e) := by
    intro i
    induction i with
    | zero => rw [pow_zero, one_mul]
    | succ i ih => rw [pow_succ, mul_assoc, h1e.eq, ih]
  let Lη := Localization.Away (1 - e)
  have hunit : IsUnit (algebraMap R Lη π) := by
    rw [← Ideal.span_singleton_eq_top, ← Set.image_singleton, ← Ideal.map_span, ← hπ']
    exact hgen
  obtain ⟨h, hh⟩ : ∃ h : H, algebraMap R H π * h * (1 - e) = 1 - e := by
    obtain ⟨z, hz⟩ := hunit.exists_right_inv
    obtain ⟨⟨h, d⟩, hzh⟩ := IsLocalization.mk'_surjective (Submonoid.powers (1 - e)) z
    obtain ⟨k, hk'⟩ := (Submonoid.mem_powers_iff _ _).mp d.2
    have hk : z * algebraMap H Lη (d : H) = algebraMap H Lη h := by
      rw [← hzh]; exact IsLocalization.mk'_spec Lη h d
    have hzero : algebraMap H Lη (algebraMap R H π * h - (d : H)) = 0 := by
      rw [map_sub, map_mul, ← hk, ← mul_assoc, ← IsScalarTower.algebraMap_apply, hz, one_mul, sub_self]
    obtain ⟨⟨m', hm'⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (1 - e)) Lη _).mp hzero
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hm'
    refine ⟨h, ?_⟩
    have hj' : (1 - e) ^ j * (algebraMap R H π * h - (1 - e) ^ k) = 0 := by rw [hk']; exact hj
    have e1 : (1 - e) ^ j * (algebraMap R H π * h) = (1 - e) ^ (j + k) := by linear_combination hj'
    have e2 := congrArg (fun t => (1 - e) * t) e1
    have l1 : (1 - e) * ((1 - e) ^ j * (algebraMap R H π * h)) = algebraMap R H π * h * (1 - e) := by
      rw [← mul_assoc, mul_comm (1 - e) ((1 - e) ^ j), hpow]; ring
    have l2 : (1 - e) * (1 - e) ^ (j + k) = 1 - e := by rw [mul_comm, hpow]
    rw [l1, l2] at e2
    exact e2

  have h1f1e : (1 - f) * (1 - e) = 1 - f := by
    have : f * e = e := hfe
    calc (1 - f) * (1 - e) = 1 - e - f + f * e := by ring
      _ = 1 - f := by rw [this]; ring
  set x := h * (1 - f) with hx
  have hπx : algebraMap R H π * x = 1 - f := by
    have h3 := congrArg (fun t => t * (1 - f)) hh
    rw [mul_comm (1 - e) (1 - f), h1f1e] at h3
    calc algebraMap R H π * x = algebraMap R H π * h * ((1 - f) * (1 - e)) := by rw [h1f1e, hx, mul_assoc]
      _ = algebraMap R H π * h * (1 - e) * (1 - f) := by ring
      _ = 1 - f := h3
  have h1fB : (1 - f) ∈ B := Subalgebra.sub_mem _ (Subalgebra.one_mem _) hfK
  let jHH : H ⊗[R] H' → K ⊗[R] (H ⊗[R] H') := fun w => (1 : K) ⊗ₜ[R] w
  have hjHH : Function.Injective jHH := one_tmul_injective R K (M := H ⊗[R] H')
  have hxB : x ∈ B := by
    show HopfAlgebra.coaction qc x = x ⊗ₜ[R] 1
    have hρ : HopfAlgebra.coaction qc (1 - f) = (1 - f) ⊗ₜ[R] 1 := h1fB
    have hπx' : π • x = 1 - f := by rw [Algebra.smul_def, hπx]
    have hsm : π • (HopfAlgebra.coaction qc x - x ⊗ₜ[R] 1) = 0 := by
      rw [smul_sub, ← map_smul, TensorProduct.smul_tmul', hπx', hρ, sub_self]
    by_cases hπ0 : π = 0
    · have hx0 : x = 0 := by
        have : (1 : H) - f = 0 := by rw [← hπx', hπ0, zero_smul]
        rw [hx, this, mul_zero]
      rw [hx0, map_zero, TensorProduct.zero_tmul]
    · have hK : algebraMap R K π ≠ 0 := fun h0 =>
        hπ0 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R K) π h0)
      have : jHH (HopfAlgebra.coaction qc x - x ⊗ₜ[R] 1) = 0 := by
        have h1 : algebraMap R K π • jHH (HopfAlgebra.coaction qc x - x ⊗ₜ[R] 1) = 0 := by
          show algebraMap R K π • ((1 : K) ⊗ₜ[R] _) = 0
          rw [algebraMap_smul, ← TensorProduct.tmul_smul, hsm, TensorProduct.tmul_zero]
        exact (smul_eq_zero.mp h1).resolve_left hK
      exact sub_eq_zero.mp (hjHH (this.trans (by simp [jHH])))

  let j : H →ₗ[R] K ⊗[R] H := TensorProduct.mk R K H 1
  have hjinj : Function.Injective j := one_tmul_injective R K (M := H)
  let Y : Set H := {y | ∃ b ∈ B, y = b * (1 - f)}
  have hYB : Y ⊆ B := by rintro _ ⟨b, hb, rfl⟩; exact Subalgebra.mul_mem _ hb h1fB
  let W : Submodule K (K ⊗[R] H) := Submodule.span K (j '' Y)
  obtain ⟨G, hG⟩ : W.FG := IsNoetherian.noetherian W
  have hgen' : ∀ g : K ⊗[R] H, g ∈ G → ∃ F : Finset H, (↑F : Set H) ⊆ Y ∧ g ∈ Submodule.span K (j '' ↑F) := by
    intro g hg
    have hgW : g ∈ Submodule.span K (j '' Y) := by
      show g ∈ W
      rw [← hG]
      exact Submodule.subset_span hg
    obtain ⟨F', hF'sub, hgF'⟩ := Submodule.mem_span_finite_of_mem_span hgW
    have hpb : ∀ t : K ⊗[R] H, t ∈ F' → ∃ y ∈ Y, j y = t := fun t ht => hF'sub ht
    choose! pb hpbY hpbj using hpb
    refine ⟨F'.image pb, ?_, ?_⟩
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact hpbY t ht
    · refine Submodule.span_mono ?_ hgF'
      intro t ht
      exact ⟨pb t, Finset.mem_coe.mpr (Finset.mem_image_of_mem pb (Finset.mem_coe.mp ht)), hpbj t ht⟩
  choose! Fg hFgY hFg using hgen'
  let T : Finset H := G.biUnion Fg
  have hTY : (↑T : Set H) ⊆ Y := by
    intro y hy
    obtain ⟨g, hg, hy'⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
    exact hFgY g hg (Finset.mem_coe.mpr hy')
  have hWT : W ≤ Submodule.span K (j '' ↑T) := by
    rw [show W = Submodule.span K ↑G from hG.symm]
    refine Submodule.span_le.mpr fun g hg => ?_
    refine Submodule.span_mono (Set.image_mono ?_) (hFg g (Finset.mem_coe.mp hg))
    intro y hy
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg, Finset.mem_coe.mp hy⟩)
  refine ⟨x, hxB, T, hTY.trans hYB, fun b hb => ?_⟩

  have hbW : j (b * (1 - f)) ∈ Submodule.span K (j '' ↑T) := hWT (Submodule.subset_span ⟨_, ⟨b, hb, rfl⟩, rfl⟩)
  obtain ⟨n, k, g, hsum⟩ := Submodule.mem_span_set'.mp hbW
  have hg : ∀ i, ∃ t ∈ (↑T : Set H), j t = (g i : K ⊗[R] H) := fun i => (g i).2
  choose t htT htj using hg
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) (Finset.univ.image k)
  have hr : ∀ i, ∃ r : R, algebraMap R K r = (s : R) • k i := fun i =>
    hs (k i) (Finset.mem_image_of_mem k (Finset.mem_univ i))
  choose r hr using hr

  set c := ∑ i, r i • t i with hc
  have hcT : c ∈ Submodule.span R (↑T : Set H) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (htT i))
  have hsb : (s : R) • (b * (1 - f)) = c := by
    apply hjinj
    show j ((s : R) • (b * (1 - f))) = j c
    rw [map_smul, hc, map_sum]
    simp_rw [map_smul]
    rw [← algebraMap_smul K (s : R) (j (b * (1 - f))), ← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← htj, smul_smul]
    have : algebraMap R K (s : R) * k i = algebraMap R K (r i) := by rw [hr i, Algebra.smul_def]
    rw [this, algebraMap_smul]

  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  obtain ⟨m, u, hum⟩ := exists_eq_unit_mul_pow_generator R π hπ' (s : R) hs0
  refine ⟨m, ((u⁻¹ : Rˣ) : R) • c, Submodule.smul_mem _ _ hcT, ?_⟩
  have hπm : π ^ m • (b * (1 - f)) = ((u⁻¹ : Rˣ) : R) • c := by
    rw [← hsb, hum, smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
  have hkey : ∀ i : ℕ, x ^ i * (π ^ i • (b * (1 - f))) = b * (1 - f) := by
    intro i
    rw [Algebra.smul_def, map_pow, ← mul_assoc, ← mul_pow, mul_comm x, hπx]
    have h1f : IsIdempotentElem (1 - f) := hf.one_sub
    induction i with
    | zero => rw [pow_zero, one_mul]
    | succ i ih => rw [pow_succ, mul_assoc, ← mul_assoc (1 - f) b, mul_comm (1 - f) b, mul_assoc b, h1f.eq, ih]
  rw [← hπm, hkey]

end S17S52

open S17S52 in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (e' : H') (he' : IsIdempotentElem e') (hfin' : Module.Finite R (Localization.Away e'))
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (IsLocalRing.maximalIdeal R) = ⊤)
    (hee' : qc e = e')
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0) :
    Algebra.FiniteType R ↥(HopfAlgebra.hopfKer qc) := by
  classical
  set B := HopfAlgebra.hopfKer qc with hB
  obtain ⟨S, hSB, hS⟩ := exists_finset_span_mul_orbit R K H H' qc e he hfin hgen f hf hfK hfe hmin
  obtain ⟨x, hxB, T, hTB, hT⟩ := exists_inv_uniformizer_mem_and_finset R K H H' qc e he hfin hgen f hf hfK hfe hmin

  rw [← Subalgebra.fg_iff_finiteType]
  refine ⟨insert f (insert x (S ∪ T)), le_antisymm ?_ ?_⟩
  ·
    apply Algebra.adjoin_le
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union] at hy
    rcases hy with rfl | rfl | hy | hy
    · exact hfK
    · exact hxB
    · exact hSB hy
    · exact hTB hy
  ·
    intro b hb
    have hsplit : b = b * f + b * (1 - f) := by ring
    rw [hsplit]
    set Gen : Set H := ↑(insert f (insert x (S ∪ T))) with hGen
    have hS' : (↑S : Set H) ⊆ Gen := by
      intro y hy; simp only [hGen, Finset.coe_insert, Finset.coe_union]; exact Or.inr (Or.inr (Or.inl hy))
    have hT' : (↑T : Set H) ⊆ Gen := by
      intro y hy; simp only [hGen, Finset.coe_insert, Finset.coe_union]; exact Or.inr (Or.inr (Or.inr hy))
    have hx' : x ∈ Algebra.adjoin R Gen := Algebra.subset_adjoin (by simp [hGen])
    refine Subalgebra.add_mem _ ?_ ?_
    · have h1 := hS b hb
      exact (Submodule.span_le.mpr (fun y hy => Algebra.subset_adjoin (hS' hy)) : Submodule.span R (↑S : Set H) ≤
        Subalgebra.toSubmodule (Algebra.adjoin R Gen)) h1
    · obtain ⟨n, c, hc, hbc⟩ := hT b hb
      rw [hbc]
      have hc' : c ∈ Algebra.adjoin R Gen :=
        (Submodule.span_le.mpr (fun y hy => Algebra.subset_adjoin (hT' hy)) : Submodule.span R (↑T : Set H) ≤
          Subalgebra.toSubmodule (Algebra.adjoin R Gen)) hc
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hx' n) hc'

end S_HopfAlgebra_finiteType_hopfKer_of_finitePartIdempotent
end P2MW
export P2MW.S_HopfAlgebra_finiteType_hopfKer_of_finitePartIdempotent (solution)
