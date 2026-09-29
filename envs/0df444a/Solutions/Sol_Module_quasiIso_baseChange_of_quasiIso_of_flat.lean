-- Prove2me | solution 1 for Module.quasiIso_baseChange_of_quasiIso_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9ac4097a-7de5-5867-921e-03ce8a7567b7

import Mathlib
import Theorems.Thm_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_quasiIso_baseChange_of_quasiIso_of_flat

set_option autoImplicit false

universe u

open TensorProduct

namespace QisoBC

theorem flat_prod {R : Type u} [CommRing R] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ Q
  have key : ∀ z, TensorProduct.prodRight R R P M N (Q.subtype.rTensor (M × N) z) =
      (Q.subtype.rTensor M).prodMap (Q.subtype.rTensor N) (TensorProduct.prodRight R R (↥Q) M N z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul q m => simp [LinearMap.rTensor_tmul, TensorProduct.prodRight_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  intro z₁ z₂ h
  have h' := congrArg (TensorProduct.prodRight R R P M N) h
  rw [key, key, LinearMap.prodMap_apply, LinearMap.prodMap_apply, Prod.mk.injEq] at h'
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) Q.subtype Q.injective_subtype h'.1
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := N) Q.subtype Q.injective_subtype h'.2
  exact (TensorProduct.prodRight R R (↥Q) M N).injective (Prod.ext h1 h2)

variable {S : Type u} [CommRing S]
variable (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]
variable (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module S (C i)]

def Cone : ℕ → Type u
  | 0 => K 0
  | i + 1 => K (i + 1) × C i

scoped instance instACG : ∀ i, AddCommGroup (Cone K C i)
  | 0 => inferInstanceAs (AddCommGroup (K 0))
  | i + 1 => inferInstanceAs (AddCommGroup (K (i + 1) × C i))

scoped instance instMod : ∀ i, Module S (Cone K C i)
  | 0 => inferInstanceAs (Module S (K 0))
  | i + 1 => inferInstanceAs (Module S (K (i + 1) × C i))

theorem flat_cone [∀ i, Module.Flat S (K i)] [∀ i, Module.Flat S (C i)] :
    ∀ i, Module.Flat S (Cone K C i)
  | 0 => inferInstanceAs (Module.Flat S (K 0))
  | i + 1 => by
      haveI := flat_prod (R := S) (K (i + 1)) (C i)
      exact inferInstanceAs (Module.Flat S (K (i + 1) × C i))

omit [∀ i, AddCommGroup (K i)] [∀ i, AddCommGroup (C i)] [∀ i, Module S (K i)] [∀ i, Module S (C i)] in
theorem subsingleton_cone (n : ℕ) (hK : ∀ i, n < i → Subsingleton (K i))
    (hC : ∀ i, n < i → Subsingleton (C i)) : ∀ i, n + 2 ≤ i → Subsingleton (Cone K C i)
  | 0 => fun h => absurd h (by omega)
  | i + 1 => fun h => by
      haveI := hK (i + 1) (by omega); haveI := hC i (by omega)
      exact inferInstanceAs (Subsingleton (K (i + 1) × C i))

variable (δ : ∀ i, K i →ₗ[S] K (i + 1)) (d : ∀ i, C i →ₗ[S] C (i + 1)) (φ : ∀ i, K i →ₗ[S] C i)

def D : ∀ i, Cone K C i →ₗ[S] Cone K C (i + 1)
  | 0 => LinearMap.prod (δ 0) (φ 0)
  | i + 1 => LinearMap.prod (δ (i + 1) ∘ₗ LinearMap.fst S (K (i + 1)) (C i))
      (φ (i + 1) ∘ₗ LinearMap.fst S (K (i + 1)) (C i) - d i ∘ₗ LinearMap.snd S (K (i + 1)) (C i))

theorem D_zero_apply (x : K 0) : (D K C δ d φ 0 x : K 1 × C 0) = (δ 0 x, φ 0 x) := rfl

theorem D_succ_apply (i : ℕ) (z : K (i + 1) × C i) :
    (D K C δ d φ (i + 1) z : K (i + 2) × C (i + 1)) = (δ (i + 1) z.1, φ (i + 1) z.1 - d i z.2) := rfl

theorem D_comp_D (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i) : ∀ i, D K C δ d φ (i + 1) ∘ₗ D K C δ d φ i = 0
  | 0 => by
      refine LinearMap.ext fun x => ?_
      show ((δ 1 (δ 0 x), φ 1 (δ 0 x) - d 0 (φ 0 x)) : K 2 × C 1) = 0
      have h1 := congrArg (fun f => f x) (hδδ 0)
      have h2 := congrArg (fun f => f x) (hφ 0)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 h2
      rw [h1, h2, sub_self]; rfl
  | i + 1 => by
      refine LinearMap.ext fun z => ?_
      show ((δ (i + 2) (δ (i + 1) z.1), φ (i + 2) (δ (i + 1) z.1) - d (i + 1) (φ (i + 1) z.1 - d i z.2)) :
        K (i + 3) × C (i + 2)) = 0
      have h1 := congrArg (fun f => f z.1) (hδδ (i + 1))
      have h2 := congrArg (fun f => f z.1) (hφ (i + 1))
      have h3 := congrArg (fun f => f z.2) (hdd i)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 h2 h3
      rw [h1, map_sub, h3, h2, sub_zero, sub_self]; rfl

theorem cone_exact (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i)) :
    LinearMap.ker (D K C δ d φ 0) = ⊥ ∧
      ∀ i, LinearMap.ker (D K C δ d φ (i + 1)) ≤ LinearMap.range (D K C δ d φ i) := by
  have hφ' : ∀ i (x : K i), d i (φ i x) = φ (i + 1) (δ i x) := fun i x => by
    have h := congrArg (fun f => f x) (hφ i); simpa using h
  refine ⟨?_, ?_⟩
  · rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx' : ((δ 0 x, φ 0 x) : K 1 × C 0) = 0 := hx
    rw [Prod.mk_eq_zero] at hx'
    exact h0inj x hx'.1 hx'.2
  · rintro (_ | i) z hz
    ·
      change K 1 × C 0 at z
      have hz' : ((δ 1 z.1, φ 1 z.1 - d 0 z.2) : K 2 × C 1) = 0 := hz
      rw [Prod.mk_eq_zero, sub_eq_zero] at hz'
      obtain ⟨x', hx'⟩ := hinj 0 z.1 hz'.1 ⟨z.2, hz'.2.symm⟩
      have hw : d 0 (z.2 - φ 0 x') = 0 := by rw [map_sub, hφ' 0 x', hx', hz'.2, sub_self]
      obtain ⟨x'', hx''δ, hx''φ⟩ := h0surj (z.2 - φ 0 x') hw
      refine ⟨x' + x'', ?_⟩
      show ((δ 0 (x' + x''), φ 0 (x' + x'')) : K 1 × C 0) = z
      rw [map_add, map_add, hx', hx''δ, hx''φ, add_zero, add_sub_cancel]
    ·
      change K (i + 2) × C (i + 1) at z
      have hz' : ((δ (i + 2) z.1, φ (i + 2) z.1 - d (i + 1) z.2) : K (i + 3) × C (i + 2)) = 0 := hz
      rw [Prod.mk_eq_zero, sub_eq_zero] at hz'
      obtain ⟨x', hx'⟩ := hinj (i + 1) z.1 hz'.1 ⟨z.2, hz'.2.symm⟩
      have hw : d (i + 1) (z.2 - φ (i + 1) x') = 0 := by
        rw [map_sub, hφ' (i + 1) x', hx', hz'.2, sub_self]
      obtain ⟨x'', hδ'', y'', hy''⟩ := hsurj i (z.2 - φ (i + 1) x') hw
      refine ⟨((x' + x'', y'') : K (i + 1) × C i), ?_⟩
      show ((δ (i + 1) (x' + x''), φ (i + 1) (x' + x'') - d i y'') : K (i + 2) × C (i + 1)) = z
      rw [map_add, map_add, hx', hδ'', hy'', add_zero]
      ext
      · rfl
      · show φ (i + 1) x' + φ (i + 1) x'' - (φ (i + 1) x'' - (z.2 - φ (i + 1) x')) = z.2
        abel

theorem qiso_of_cone_exact (hex0 : LinearMap.ker (D K C δ d φ 0) = ⊥)
    (hex : ∀ i, LinearMap.ker (D K C δ d φ (i + 1)) ≤ LinearMap.range (D K C δ d φ i)) :
    (∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0) ∧
    (∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y) ∧
    (∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i)) ∧
    (∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hδ hφ
    have hx : x ∈ LinearMap.ker (D K C δ d φ 0) := by
      show ((δ 0 x, φ 0 x) : K 1 × C 0) = 0
      rw [hδ, hφ]; rfl
    rw [hex0] at hx
    exact hx
  · intro y hy
    have hz : ((0, y) : K 1 × C 0) ∈ LinearMap.ker (D K C δ d φ (0 + 1)) := by
      show ((δ 1 0, φ 1 0 - d 0 y) : K 2 × C 1) = 0
      rw [map_zero, map_zero, hy, sub_zero]; rfl
    obtain ⟨x, hx⟩ := hex 0 hz
    have hx' : ((δ 0 x, φ 0 x) : K 1 × C 0) = (0, y) := hx
    rw [Prod.mk.injEq] at hx'
    exact ⟨x, hx'.1, hx'.2⟩
  · intro i x hδ hφ
    obtain ⟨y, hy⟩ := hφ
    have hz : ((x, y) : K (i + 1) × C i) ∈ LinearMap.ker (D K C δ d φ (i + 1)) := by
      show ((δ (i + 1) x, φ (i + 1) x - d i y) : K (i + 2) × C (i + 1)) = 0
      rw [hδ, hy, sub_self]; rfl
    obtain ⟨w, hw⟩ := hex i hz
    cases i with
    | zero =>
        have hw' : ((δ 0 w, φ 0 w) : K 1 × C 0) = (x, y) := hw
        rw [Prod.mk.injEq] at hw'
        exact ⟨w, hw'.1⟩
    | succ j =>
        change K (j + 1) × C j at w
        have hw' : ((δ (j + 1) w.1, φ (j + 1) w.1 - d j w.2) : K (j + 2) × C (j + 1)) = (x, y) := hw
        rw [Prod.mk.injEq] at hw'
        exact ⟨w.1, hw'.1⟩
  · intro i y hy
    have hz : ((0, y) : K (i + 2) × C (i + 1)) ∈ LinearMap.ker (D K C δ d φ (i + 1 + 1)) := by
      show ((δ (i + 2) 0, φ (i + 2) 0 - d (i + 1) y) : K (i + 3) × C (i + 2)) = 0
      rw [map_zero, map_zero, hy, sub_zero]; rfl
    obtain ⟨w, hw⟩ := hex (i + 1) hz
    change K (i + 1) × C i at w
    have hw' : ((δ (i + 1) w.1, φ (i + 1) w.1 - d i w.2) : K (i + 2) × C (i + 1)) = (0, y) := hw
    rw [Prod.mk.injEq] at hw'
    refine ⟨w.1, hw'.1, w.2, ?_⟩
    rw [← hw'.2, sub_sub_cancel]

theorem exact_transfer {A : Type u} [CommRing A] (E E' : ℕ → Type u)
    [∀ i, AddCommGroup (E i)] [∀ i, Module A (E i)] [∀ i, AddCommGroup (E' i)] [∀ i, Module A (E' i)]
    (D₁ : ∀ i, E i →ₗ[A] E (i + 1)) (D₂ : ∀ i, E' i →ₗ[A] E' (i + 1)) (e : ∀ i, E i ≃ₗ[A] E' i)
    (he : ∀ i z, e (i + 1) (D₁ i z) = D₂ i (e i z))
    (h0 : LinearMap.ker (D₁ 0) = ⊥) (hex : ∀ i, LinearMap.ker (D₁ (i + 1)) ≤ LinearMap.range (D₁ i)) :
    LinearMap.ker (D₂ 0) = ⊥ ∧ ∀ i, LinearMap.ker (D₂ (i + 1)) ≤ LinearMap.range (D₂ i) := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.ker_eq_bot'] at h0 ⊢
    intro z' hz'
    obtain ⟨z, rfl⟩ := (e 0).surjective z'
    rw [← he, LinearEquiv.map_eq_zero_iff] at hz'
    rw [h0 z hz', map_zero]
  · intro i z' hz'
    obtain ⟨z, rfl⟩ := (e (i + 1)).surjective z'
    rw [LinearMap.mem_ker, ← he, LinearEquiv.map_eq_zero_iff] at hz'
    obtain ⟨w, hw⟩ := hex i hz'
    exact ⟨e i w, by rw [← he, hw]⟩

section baseChange

variable {R : Type u} [CommRing R]
variable (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
variable (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
variable (A : Type u) [CommRing A] [Algebra R A]

noncomputable def coneBC :
    ∀ i, A ⊗[R] Cone K C i ≃ₗ[A] Cone (fun j => A ⊗[R] K j) (fun j => A ⊗[R] C j) i
  | 0 => LinearEquiv.refl A (A ⊗[R] K 0)
  | i + 1 => TensorProduct.prodRight R A A (K (i + 1)) (C i)

variable (δ : ∀ i, K i →ₗ[R] K (i + 1)) (d : ∀ i, C i →ₗ[R] C (i + 1)) (φ : ∀ i, K i →ₗ[R] C i)

theorem coneBC_comm : ∀ (i : ℕ) (z : A ⊗[R] Cone K C i),
    coneBC K C A (i + 1) ((D K C δ d φ i).baseChange A z) =
      D (fun j => A ⊗[R] K j) (fun j => A ⊗[R] C j) (fun j => (δ j).baseChange A)
        (fun j => (d j).baseChange A) (fun j => (φ j).baseChange A) i (coneBC K C A i z)
  | 0, z => by
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x =>
          change K 0 at x
          show TensorProduct.prodRight R A A (K 1) (C 0) (a ⊗ₜ[R] ((δ 0 x, φ 0 x) : K 1 × C 0)) =
            (((δ 0).baseChange A (a ⊗ₜ[R] x), (φ 0).baseChange A (a ⊗ₜ[R] x)) :
              (A ⊗[R] K 1) × (A ⊗[R] C 0))
          rfl
  | i + 1, z => by
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a z =>
          change K (i + 1) × C i at z
          show TensorProduct.prodRight R A A (K (i + 2)) (C (i + 1))
              (a ⊗ₜ[R] ((δ (i + 1) z.1, φ (i + 1) z.1 - d i z.2) : K (i + 2) × C (i + 1))) =
            (((δ (i + 1)).baseChange A (a ⊗ₜ[R] z.1),
              (φ (i + 1)).baseChange A (a ⊗ₜ[R] z.1) - (d i).baseChange A (a ⊗ₜ[R] z.2)) :
              (A ⊗[R] K (i + 2)) × (A ⊗[R] C (i + 1)))
          rw [TensorProduct.prodRight_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
            LinearMap.baseChange_tmul, TensorProduct.tmul_sub]

end baseChange

end QisoBC
p2m_reactivate "P2MW.S_Module_quasiIso_baseChange_of_quasiIso_of_flat.QisoBC"

open QisoBC in
theorem solution
    (R : Type u) [CommRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Flat R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hKbdd : ∀ i, n < i → Subsingleton (K i)) (hCbdd : ∀ i, n < i → Subsingleton (C i))
    (φ : ∀ i, K i →ₗ[R] C i) (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    (∀ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 → (φ 0).baseChange A x = 0 → x = 0) ∧
    (∀ y : A ⊗[R] C 0, (d 0).baseChange A y = 0 →
      ∃ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 ∧ (φ 0).baseChange A x = y) ∧
    (∀ (i : ℕ) (x : A ⊗[R] K (i + 1)), (δ (i + 1)).baseChange A x = 0 →
      (φ (i + 1)).baseChange A x ∈ LinearMap.range ((d i).baseChange A) →
        x ∈ LinearMap.range ((δ i).baseChange A)) ∧
    (∀ (i : ℕ) (y : A ⊗[R] C (i + 1)), (d (i + 1)).baseChange A y = 0 →
      ∃ x : A ⊗[R] K (i + 1), (δ (i + 1)).baseChange A x = 0 ∧
        (φ (i + 1)).baseChange A x - y ∈ LinearMap.range ((d i).baseChange A)) := by
  obtain ⟨hR0, hR⟩ := cone_exact K C δ d φ hφ h0inj h0surj hinj hsurj
  haveI hflat : ∀ i, Module.Flat R (Cone K C i) := flat_cone K C
  obtain ⟨hA0, hA⟩ := Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact
    (Cone K C) (D K C δ d φ) (D_comp_D K C δ d φ hδδ hdd hφ) (n + 2)
    (subsingleton_cone K C n hKbdd hCbdd) hR0 hR A
  obtain ⟨hB0, hB⟩ := exact_transfer (fun i => A ⊗[R] Cone K C i)
    (Cone (fun j => A ⊗[R] K j) (fun j => A ⊗[R] C j))
    (fun i => (D K C δ d φ i).baseChange A)
    (D (fun j => A ⊗[R] K j) (fun j => A ⊗[R] C j) (fun j => (δ j).baseChange A)
      (fun j => (d j).baseChange A) (fun j => (φ j).baseChange A))
    (coneBC K C A) (coneBC_comm K C A δ d φ) hA0 hA
  exact qiso_of_cone_exact (fun j => A ⊗[R] K j) (fun j => A ⊗[R] C j) (fun j => (δ j).baseChange A)
    (fun j => (d j).baseChange A) (fun j => (φ j).baseChange A) hB0 hB

end S_Module_quasiIso_baseChange_of_quasiIso_of_flat
end P2MW
export P2MW.S_Module_quasiIso_baseChange_of_quasiIso_of_flat (solution)
