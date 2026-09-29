-- Prove2me | solution 1 for NgoFL.isogeny_weyl_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T23:06:08.753005+00:00
-- url     : https://prove2.me/submissions/63a978ac-5735-4e7b-a23c-19f9cff32131

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant
import Definitions.Def_NgoRootDatumIsogeny

/-!
# Solution: an isogeny of root data conjugates one Weyl group onto the other

The mathematical content is the "same bijection, same constants" point of Ngô 1.12.4: if
`ψ^*(α₂) = c • α₁` then automatically `ψ_*(α₁ᵛ) = c • α₂ᵛ`.  This is *not* part of
`IsRootDatumIsogeny`, which only supplies a root-line bijection and a coroot-line bijection
with a priori unrelated constants, so it has to be proved (`coroot_match` below).

The proof is the reflection-uniqueness argument behind
`Module.Dual.eq_of_preReflection_mapsTo`, run at the level of root *lines* rather than roots
(necessary, because an isogeny only maps roots to nonzero multiples of roots):

* put `u := c⁻¹ • ψ_*(α₁ᵛ)`; the transpose axiom gives `⟨α₂, u⟩ = 2`;
* the map `T m = m - ⟨m,u⟩ • α₂` is `(ψ^*)⁻¹ ∘ s_{α₁} ∘ ψ^*`, hence sends every root to a
  nonzero multiple of a root;
* with `v := u - α₂ᵛ`, the map `R m = m - ⟨m,v⟩ • α₂` is `T ∘ s_{α₂}`, so it does the same,
  and `Rⁿ m = m - n⟨m,v⟩ • α₂` because `⟨α₂,v⟩ = 0`;
* pigeonhole on `n ↦` (an index whose root line carries `Rⁿ α_j`) forces `⟨α_j, v⟩ = 0`;
* the roots span, so `v = 0` by perfectness of the pairing, i.e. `u = α₂ᵛ`.

The rest is the reflection computation of Ngô 1.12.4 and a subgroup-closure argument.
-/

open NgoFL

/-- **Key lemma.** In an isogeny of root data the root-line bijection and the coroot-line
bijection are the same bijection, with the same proportionality constant. -/
private lemma coroot_match {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module ℚ M₁]
    [AddCommGroup N₁] [Module ℚ N₁] [AddCommGroup M₂] [Module ℚ M₂] [AddCommGroup N₂]
    [Module ℚ N₂] [Fintype ι₂] (P₁ : RootPairing ι₁ ℚ M₁ N₁) (P₂ : RootPairing ι₂ ℚ M₂ N₂)
    [P₂.IsRootSystem] {b₁ : Set ι₁} {b₂ : Set ι₂} {psiStar : M₂ ≃ₗ[ℚ] M₁}
    {psiLower : N₁ ≃ₗ[ℚ] N₂} (h : IsRootDatumIsogeny P₁ P₂ b₁ b₂ psiStar psiLower)
    {i₁ : ι₁} {i₂ : ι₂} {c : ℚ} (hc : c ≠ 0)
    (hroot : psiStar (P₂.root i₂) = c • P₁.root i₁) :
    psiLower (P₁.coroot i₁) = c • P₂.coroot i₂ := by
  obtain ⟨u, hu_def⟩ : ∃ u : N₂, u = c⁻¹ • psiLower (P₁.coroot i₁) := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v : N₂, v = u - P₂.coroot i₂ := ⟨_, rfl⟩
  -- `⟨α₂, u⟩ = 2`.
  have hu2 : P₂.toLinearMap (P₂.root i₂) u = 2 := by
    rw [hu_def, map_smul, smul_eq_mul, ← h.transpose (P₂.root i₂) (P₁.coroot i₁), hroot]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same]
    field_simp
  have hvi2 : P₂.toLinearMap (P₂.root i₂) v = 0 := by
    rw [hv_def, map_sub, hu2, RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same,
      sub_self]
  -- `T m = m - ⟨m,u⟩ • α₂` sends each root to a nonzero multiple of a root.
  have hT : ∀ j : ι₂, ∃ (k : ι₂) (μ : ℚ), μ ≠ 0 ∧
      P₂.root j - (P₂.toLinearMap (P₂.root j) u) • P₂.root i₂ = μ • P₂.root k := by
    intro j
    obtain ⟨m, cj, hcj, hmj⟩ := h.root_line j
    obtain ⟨k, c', hc', hk⟩ := h.root_line_surjective (P₁.reflectionPerm i₁ m)
    have ht : P₂.toLinearMap (P₂.root j) u = c⁻¹ * (cj * P₁.pairing m i₁) := by
      rw [hu_def, map_smul, smul_eq_mul, ← h.transpose (P₂.root j) (P₁.coroot i₁), hmj]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
        RootPairing.root_coroot_eq_pairing]
    have hrefl : P₁.root (P₁.reflectionPerm i₁ m)
        = P₁.root m - P₁.pairing m i₁ • P₁.root i₁ := by
      rw [P₁.root_reflectionPerm, P₁.reflection_apply_root]
    refine ⟨k, cj / c', div_ne_zero hcj hc', ?_⟩
    apply psiStar.injective
    simp only [map_sub, map_smul]
    rw [hmj, hroot, hk, hrefl, ht]
    match_scalars
    all_goals (field_simp; try ring)
  -- `R m = m - ⟨m,v⟩ • α₂` (which is `T ∘ s_{α₂}`) does the same.
  have hR : ∀ j : ι₂, ∃ (k : ι₂) (μ : ℚ), μ ≠ 0 ∧
      P₂.root j - (P₂.toLinearMap (P₂.root j) v) • P₂.root i₂ = μ • P₂.root k := by
    intro j
    obtain ⟨k, μ, hμ, hkey⟩ := hT (P₂.reflectionPerm i₂ j)
    refine ⟨k, μ, hμ, ?_⟩
    rw [← hkey]
    have hrj : P₂.root (P₂.reflectionPerm i₂ j)
        = P₂.root j - P₂.pairing j i₂ • P₂.root i₂ := by
      rw [P₂.root_reflectionPerm, P₂.reflection_apply_root]
    have hvj : P₂.toLinearMap (P₂.root j) v
        = P₂.toLinearMap (P₂.root j) u - P₂.pairing j i₂ := by
      rw [hv_def, map_sub, RootPairing.root_coroot_eq_pairing]
    rw [hvj, hrj]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu2]
    match_scalars <;> ring
  -- Iterating: `Rⁿ α_j = α_j - n⟨α_j,v⟩ • α₂` is still a nonzero multiple of a root.
  have hIter : ∀ (j : ι₂) (n : ℕ), ∃ (k : ι₂) (μ : ℚ), μ ≠ 0 ∧
      P₂.root j - ((n : ℚ) * P₂.toLinearMap (P₂.root j) v) • P₂.root i₂ = μ • P₂.root k := by
    intro j n
    induction n with
    | zero => exact ⟨j, 1, one_ne_zero, by simp⟩
    | succ n ih =>
        obtain ⟨k, μ, hμ, hkn⟩ := ih
        obtain ⟨k', μ', hμ', hk'⟩ := hR k
        have hpair : P₂.toLinearMap (P₂.root j) v = μ * P₂.toLinearMap (P₂.root k) v := by
          have hc0 := congrArg (fun m : M₂ => P₂.toLinearMap m v) hkn
          simpa only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
            smul_eq_mul, hvi2, mul_zero, sub_zero] using hc0
        refine ⟨k', μ * μ', mul_ne_zero hμ hμ', ?_⟩
        push_cast
        calc P₂.root j - (((n : ℚ) + 1) * P₂.toLinearMap (P₂.root j) v) • P₂.root i₂
            = (P₂.root j - ((n : ℚ) * P₂.toLinearMap (P₂.root j) v) • P₂.root i₂)
              - (P₂.toLinearMap (P₂.root j) v) • P₂.root i₂ := by module
          _ = μ • P₂.root k - (μ * P₂.toLinearMap (P₂.root k) v) • P₂.root i₂ := by
              rw [hkn, hpair]
          _ = μ • (P₂.root k - (P₂.toLinearMap (P₂.root k) v) • P₂.root i₂) := by module
          _ = μ • (μ' • P₂.root k') := by rw [hk']
          _ = (μ * μ') • P₂.root k' := by rw [smul_smul]
  -- Pigeonhole over the finitely many indices.
  have hzero : ∀ j : ι₂, P₂.toLinearMap (P₂.root j) v = 0 := by
    intro j
    by_contra ht
    choose K MU hMU hK using hIter j
    obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite K
    have h1 := hK n₁
    have h2 := hK n₂
    rw [heq] at h1
    have hA1 : P₂.toLinearMap (P₂.root j) v
        = MU n₁ * P₂.toLinearMap (P₂.root (K n₂)) v := by
      have hc0 := congrArg (fun m : M₂ => P₂.toLinearMap m v) h1
      simpa only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hvi2, mul_zero, sub_zero] using hc0
    have hA2 : P₂.toLinearMap (P₂.root j) v
        = MU n₂ * P₂.toLinearMap (P₂.root (K n₂)) v := by
      have hc0 := congrArg (fun m : M₂ => P₂.toLinearMap m v) h2
      simpa only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hvi2, mul_zero, sub_zero] using hc0
    have hs : P₂.toLinearMap (P₂.root (K n₂)) v ≠ 0 := fun hs0 =>
      ht (by rw [hA1, hs0, mul_zero])
    have hmueq : MU n₁ = MU n₂ := mul_right_cancel₀ hs (hA1.symm.trans hA2)
    have hEq : P₂.root j - ((n₁ : ℚ) * P₂.toLinearMap (P₂.root j) v) • P₂.root i₂
        = P₂.root j - ((n₂ : ℚ) * P₂.toLinearMap (P₂.root j) v) • P₂.root i₂ :=
      h1.trans (by rw [hmueq]; exact h2.symm)
    have hscal : (((n₂ : ℚ) - (n₁ : ℚ)) * P₂.toLinearMap (P₂.root j) v) • P₂.root i₂ = 0 := by
      have h0 : (P₂.root j - ((n₁ : ℚ) * P₂.toLinearMap (P₂.root j) v) • P₂.root i₂)
          - (P₂.root j - ((n₂ : ℚ) * P₂.toLinearMap (P₂.root j) v) • P₂.root i₂) = 0 := by
        rw [hEq, sub_self]
      rw [← h0]
      match_scalars <;> ring
    have hcast : ((n₂ : ℚ) - (n₁ : ℚ)) ≠ 0 := by
      have hnn : (n₂ : ℚ) ≠ (n₁ : ℚ) := by exact_mod_cast (Ne.symm hne)
      exact sub_ne_zero.mpr hnn
    have hne0 : ((n₂ : ℚ) - (n₁ : ℚ)) * P₂.toLinearMap (P₂.root j) v ≠ 0 :=
      mul_ne_zero hcast ht
    have hroot0 : P₂.root i₂ = 0 := by
      have hx := congrArg
        (fun y : M₂ => (((n₂ : ℚ) - (n₁ : ℚ)) * P₂.toLinearMap (P₂.root j) v)⁻¹ • y) hscal
      simpa only [smul_smul, inv_mul_cancel₀ hne0, one_smul, smul_zero] using hx
    have h22 := P₂.root_coroot_two i₂
    rw [hroot0] at h22
    simp at h22
  -- Perfectness of the pairing: `v = 0`.
  have hspan : Submodule.span ℚ (Set.range P₂.root) = ⊤ :=
    RootPairing.IsRootSystem.span_root_eq_top
  have hdual : (P₂.toLinearMap.flip v) = (0 : Module.Dual ℚ M₂) := by
    refine LinearMap.ext_on hspan ?_
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    simpa using hzero j
  have hv0 : v = 0 := by
    apply (P₂.toLinearMap.flip.toPerfPair).injective
    rw [map_zero]
    exact hdual
  rw [hv_def, sub_eq_zero] at hv0
  rw [hu_def] at hv0
  have hfin := congrArg (fun y : N₂ => c • y) hv0
  simpa only [smul_smul, mul_inv_cancel₀ hc, one_smul] using hfin

/-- Ngô 1.12.4: a matched pair of root lines gives a matched pair of reflections.  This is the
computation of the milestone `NgoFL.isogeny_coreflection`, with the matching of the constants
now supplied by `coroot_match` instead of being hypothesised. -/
private lemma coreflection_transport {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module ℚ M₁]
    [AddCommGroup N₁] [Module ℚ N₁] [AddCommGroup M₂] [Module ℚ M₂] [AddCommGroup N₂]
    [Module ℚ N₂] [Fintype ι₂] (P₁ : RootPairing ι₁ ℚ M₁ N₁) (P₂ : RootPairing ι₂ ℚ M₂ N₂)
    [P₂.IsRootSystem] {b₁ : Set ι₁} {b₂ : Set ι₂} {psiStar : M₂ ≃ₗ[ℚ] M₁}
    {psiLower : N₁ ≃ₗ[ℚ] N₂} (h : IsRootDatumIsogeny P₁ P₂ b₁ b₂ psiStar psiLower)
    {i₁ : ι₁} {i₂ : ι₂} {c : ℚ} (hc : c ≠ 0)
    (hroot : psiStar (P₂.root i₂) = c • P₁.root i₁) (x : N₁) :
    psiLower (P₁.coreflection i₁ x) = P₂.coreflection i₂ (psiLower x) := by
  have hcoroot : psiLower (P₁.coroot i₁) = c • P₂.coroot i₂ :=
    coroot_match P₁ P₂ h hc hroot
  have key : P₂.toLinearMap (P₂.root i₂) (psiLower x)
      = c * P₁.toLinearMap (P₁.root i₁) x := by
    rw [← h.transpose (P₂.root i₂) x, hroot]
    simp
  simp only [RootPairing.coreflection, Module.reflection_apply, map_sub,
    map_smul, hcoroot, key, smul_smul, mul_comm]

theorem solution {ι₁ ι₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [Module ℚ M₁]
    [AddCommGroup N₁] [Module ℚ N₁] [AddCommGroup M₂] [Module ℚ M₂] [AddCommGroup N₂]
    [Module ℚ N₂] [Fintype ι₁] [Fintype ι₂] (P₁ : RootPairing ι₁ ℚ M₁ N₁)
    (P₂ : RootPairing ι₂ ℚ M₂ N₂) [P₁.IsRootSystem] [P₂.IsRootSystem] [P₁.IsReduced]
    [P₂.IsReduced] (b₁ : Set ι₁) (b₂ : Set ι₂) (psiStar : M₂ ≃ₗ[ℚ] M₁)
    (psiLower : N₁ ≃ₗ[ℚ] N₂) (h : IsRootDatumIsogeny P₁ P₂ b₁ b₂ psiStar psiLower) :
    (∀ w ∈ weylSubgroup P₁ Set.univ, ∃ w' ∈ weylSubgroup P₂ Set.univ,
        ∀ x : N₁, psiLower (w x) = w' (psiLower x)) ∧
      (∀ w' ∈ weylSubgroup P₂ Set.univ, ∃ w ∈ weylSubgroup P₁ Set.univ,
        ∀ x : N₁, psiLower (w x) = w' (psiLower x)) := by
  -- each generating coreflection of `W₁` is intertwined with one of `W₂`, and conversely
  have hgen : ∀ i₁ : ι₁, ∃ i₂ : ι₂,
      ∀ x : N₁, psiLower (P₁.coreflection i₁ x) = P₂.coreflection i₂ (psiLower x) := by
    intro i₁
    obtain ⟨i₂, c, hc, hroot⟩ := h.root_line_surjective i₁
    exact ⟨i₂, fun x => coreflection_transport P₁ P₂ h hc hroot x⟩
  have hgen' : ∀ i₂ : ι₂, ∃ i₁ : ι₁,
      ∀ x : N₁, psiLower (P₁.coreflection i₁ x) = P₂.coreflection i₂ (psiLower x) := by
    intro i₂
    obtain ⟨i₁, c, hc, hroot⟩ := h.root_line i₂
    exact ⟨i₁, fun x => coreflection_transport P₁ P₂ h hc hroot x⟩
  constructor
  · intro w hw
    have hsub : weylSubgroup P₁ (Set.univ : Set ι₁) ≤
        { carrier := {f : N₁ ≃ₗ[ℚ] N₁ | ∃ f' ∈ weylSubgroup P₂ (Set.univ : Set ι₂),
            ∀ x : N₁, psiLower (f x) = f' (psiLower x)}
          one_mem' := by
            show ∃ f' ∈ weylSubgroup P₂ (Set.univ : Set ι₂),
              ∀ x : N₁, psiLower ((1 : N₁ ≃ₗ[ℚ] N₁) x) = f' (psiLower x)
            exact ⟨1, one_mem _, fun _ => rfl⟩
          mul_mem' := by
            rintro a b ⟨a', ha', hA⟩ ⟨b', hb', hB⟩
            show ∃ f' ∈ weylSubgroup P₂ (Set.univ : Set ι₂),
              ∀ x : N₁, psiLower ((a * b) x) = f' (psiLower x)
            refine ⟨a' * b', mul_mem ha' hb', fun x => ?_⟩
            simp only [LinearEquiv.mul_apply]
            rw [hA (b x), hB x]
          inv_mem' := by
            rintro a ⟨a', ha', hA⟩
            show ∃ f' ∈ weylSubgroup P₂ (Set.univ : Set ι₂),
              ∀ x : N₁, psiLower (a⁻¹ x) = f' (psiLower x)
            refine ⟨a'⁻¹, inv_mem ha', fun x => ?_⟩
            have hx := hA (a⁻¹ x)
            rw [show a (a⁻¹ x) = x from by simp] at hx
            rw [hx]
            simp } := by
      refine Subgroup.closure_le _ |>.2 ?_
      rintro f ⟨i, -, rfl⟩
      obtain ⟨i₂, hi₂⟩ := hgen i
      exact ⟨P₂.coreflection i₂, Subgroup.subset_closure ⟨i₂, Set.mem_univ _, rfl⟩, hi₂⟩
    exact hsub hw
  · intro w' hw'
    have hsub : weylSubgroup P₂ (Set.univ : Set ι₂) ≤
        { carrier := {g : N₂ ≃ₗ[ℚ] N₂ | ∃ f ∈ weylSubgroup P₁ (Set.univ : Set ι₁),
            ∀ x : N₁, psiLower (f x) = g (psiLower x)}
          one_mem' := by
            show ∃ f ∈ weylSubgroup P₁ (Set.univ : Set ι₁),
              ∀ x : N₁, psiLower (f x) = (1 : N₂ ≃ₗ[ℚ] N₂) (psiLower x)
            exact ⟨1, one_mem _, fun _ => rfl⟩
          mul_mem' := by
            rintro a b ⟨a₁, ha₁, hA⟩ ⟨b₁, hb₁, hB⟩
            show ∃ f ∈ weylSubgroup P₁ (Set.univ : Set ι₁),
              ∀ x : N₁, psiLower (f x) = (a * b) (psiLower x)
            refine ⟨a₁ * b₁, mul_mem ha₁ hb₁, fun x => ?_⟩
            simp only [LinearEquiv.mul_apply]
            rw [hA (b₁ x), hB x]
          inv_mem' := by
            rintro a ⟨a₁, ha₁, hA⟩
            show ∃ f ∈ weylSubgroup P₁ (Set.univ : Set ι₁),
              ∀ x : N₁, psiLower (f x) = a⁻¹ (psiLower x)
            refine ⟨a₁⁻¹, inv_mem ha₁, fun x => ?_⟩
            have hx := hA (a₁⁻¹ x)
            rw [show a₁ (a₁⁻¹ x) = x from by simp] at hx
            rw [hx]
            simp } := by
      refine Subgroup.closure_le _ |>.2 ?_
      rintro g ⟨i, -, rfl⟩
      obtain ⟨i₁, hi₁⟩ := hgen' i
      exact ⟨P₁.coreflection i₁, Subgroup.subset_closure ⟨i₁, Set.mem_univ _, rfl⟩, hi₁⟩
    exact hsub hw'
