-- Prove2me | solution 1 for Module.IsStablyFree.of_finite_free_resolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:32:41.955527+00:00
-- url     : https://prove2.me/submissions/799ba5a7-7e5c-4760-a226-ff1755ca07f2

import Mathlib

set_option autoImplicit false

universe u v w

namespace SerreStablyFreeAux

/-- Serre's lemma with the module in the same universe as the resolution. -/
theorem aux {A : Type u} [CommRing A] (n : ℕ) :
    ∀ (F : ℕ → Type w) [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
      [∀ i, Module.Finite A (F i)] [∀ i, Module.Free A (F i)]
      (_ : ∀ i, n < i → Subsingleton (F i))
      (d : ∀ i, F (i + 1) →ₗ[A] F i) (M : Type w) [AddCommGroup M] [Module A M]
      [Module.Projective A M] (ε : F 0 →ₗ[A] M) (_ : Function.Surjective ε)
      (_ : Function.Exact (d 0) ε) (_ : ∀ i, Function.Exact (d (i + 1)) (d i)),
      Module.IsStablyFree A M := by
  induction n with
  | zero =>
    intro F _ _ _ _ hF d M _ _ _ ε hε h0 _
    have : Subsingleton (F 1) := hF 1 (by omega)
    have hinj : Function.Injective ε := by
      refine (injective_iff_map_eq_zero ε).mpr fun y hy => ?_
      obtain ⟨z, rfl⟩ := (h0 y).mp hy
      rw [Subsingleton.elim z 0, map_zero]
    let e : F 0 ≃ₗ[A] M := LinearEquiv.ofBijective ε ⟨hinj, hε⟩
    have : Module.Free A M := Module.Free.of_equiv e
    infer_instance
  | succ n ih =>
    intro F _ _ _ _ hF d M _ _ _ ε hε h0 hd
    let K := LinearMap.ker ε
    let ε' : F 1 →ₗ[A] K := (d 0).codRestrict K (fun y =>
      LinearMap.mem_ker.mpr ((h0 (d 0 y)).mpr ⟨y, rfl⟩))
    have hε' : Function.Surjective ε' := by
      rintro ⟨k, hk⟩
      obtain ⟨y, hy⟩ := (h0 k).mp (LinearMap.mem_ker.mp hk)
      exact ⟨y, Subtype.ext hy⟩
    have h0' : Function.Exact (d 1) ε' := by
      intro y
      have : ε' y = 0 ↔ d 0 y = 0 := by
        constructor
        · intro h; simpa [ε'] using congrArg Subtype.val h
        · intro h; exact Subtype.ext h
      rw [this]
      exact hd 0 y
    obtain ⟨s, hs⟩ := Module.projective_lifting_property ε LinearMap.id hε
    have hfs (m : M) : ε (s m) = m := LinearMap.congr_fun hs m
    let r : F 0 →ₗ[A] K := (LinearMap.id - s ∘ₗ ε).codRestrict K (fun y =>
      LinearMap.mem_ker.mpr (by simp [hfs]))
    have hr : r ∘ₗ K.subtype = LinearMap.id := by
      ext k
      simp [r, LinearMap.mem_ker.mp k.2]
    have : Module.Projective A (F 0) := Module.Projective.of_free
    have : Module.Projective A K := Module.Projective.of_split K.subtype r hr
    have : Module.IsStablyFree A K :=
      ih (fun i => F (i + 1)) (fun i hi => hF (i + 1) (by omega)) (fun i => d (i + 1)) K ε' hε'
        h0' (fun i => hd (i + 1))
    have : Module.Finite A K := Module.Finite.of_surjective ε' hε'
    obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A K
    let φ : M × K →ₗ[A] F 0 := LinearMap.coprod s K.subtype
    have hφ : Function.Bijective φ := by
      refine ⟨(injective_iff_map_eq_zero φ).mpr fun ⟨m, k⟩ h => ?_, fun y => ⟨(ε y, r y), ?_⟩⟩
      · have h' : s m + (k : F 0) = 0 := h
        have hm : m = 0 := by
          have := congrArg ε h'
          rwa [map_add, hfs, LinearMap.mem_ker.mp k.2, add_zero, map_zero] at this
        subst hm
        have hk : (k : F 0) = 0 := by simpa using h'
        exact Prod.ext rfl (Subtype.ext hk)
      · simp [φ, r]
    let e : (M × K) ≃ₗ[A] F 0 := LinearEquiv.ofBijective φ hφ
    have : Module.Free A (M × (K × N)) := Module.Free.of_equiv
      ((e.symm.prodCongr (LinearEquiv.refl A N)).trans (LinearEquiv.prodAssoc A M K N))
    exact Module.IsStablyFree.of_free_prod A M (K × N)

end SerreStablyFreeAux

theorem solution {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Projective A M]
    (n : ℕ) (F : ℕ → Type w) [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    [∀ i, Module.Finite A (F i)] [∀ i, Module.Free A (F i)]
    (hF : ∀ i, n < i → Subsingleton (F i))
    (d : ∀ i, F (i + 1) →ₗ[A] F i) (ε : F 0 →ₗ[A] M) (hε : Function.Surjective ε)
    (hexact₀ : Function.Exact (d 0) ε) (hexact : ∀ i, Function.Exact (d (i + 1)) (d i)) :
    Module.IsStablyFree A M := by
  let e : (F 0 ⧸ LinearMap.ker ε) ≃ₗ[A] M := ε.quotKerEquivOfSurjective hε
  have : Module.Projective A (F 0 ⧸ LinearMap.ker ε) := Module.Projective.of_equiv e.symm
  have h0 : Function.Exact (d 0) (LinearMap.ker ε).mkQ := by
    intro y
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
    exact hexact₀ y
  have : Module.IsStablyFree A (F 0 ⧸ LinearMap.ker ε) :=
    SerreStablyFreeAux.aux n F hF d _ (LinearMap.ker ε).mkQ (Submodule.mkQ_surjective _) h0
      hexact
  exact Module.IsStablyFree.equiv e
