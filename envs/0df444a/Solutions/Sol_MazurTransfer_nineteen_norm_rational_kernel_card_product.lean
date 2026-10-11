-- Prove2me | solution 1 for MazurTransfer.nineteen_norm_rational_kernel_card_product
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T18:44:49.518793+00:00
-- url     : https://prove2.me/submissions/1eb0c842-8790-4373-869f-3c59c4743b8f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a norm pair with product nineteen and sum eight splits
the nineteen torsion of an abelian group as the product of its kernels.
If the full torsion subgroup has cardinality nineteen, the kernel cards
are nineteen and one in some order. This says nothing about geometric
kernel degrees or rank. Named downstream consumer: actual rational
Picard isogeny kernel computation and isogeny descent.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.NineteenNormRationalKernelDecomposition
variable {G : Type*} [AddCommGroup G]

def nineteenTorsion : AddSubgroup G := (19 : AddMonoid.End G).ker

private theorem reduce_ninety_six {x : G} (hx : (19 : ℕ) • x = 0) :
    (96 : ℕ) • x = x := by
  have h := congrArg (fun y : G => (5 : ℕ) • y) hx
  simp only [smul_zero, smul_smul] at h
  change (95 : ℕ) • x = 0 at h
  have he : (96 : ℕ) • x = (95 : ℕ) • x + x := by
    simpa only [one_nsmul] using add_nsmul x 95 1
  rw [he, h, zero_add]

theorem kernel_killed_nineteen (f g : G →+ G)
    (hgf : ∀ x, g (f x) = (19 : ℕ) • x) {x : G} (hx : f x = 0) :
    (19 : ℕ) • x = 0 := by
  rw [← hgf, hx, map_zero]

def kernelProductEquiv (f g : G →+ G)
    (hfg : ∀ x, f (g x) = (19 : ℕ) • x)
    (hgf : ∀ x, g (f x) = (19 : ℕ) • x)
    (hsum : ∀ x, f x + g x = (8 : ℕ) • x) :
    nineteenTorsion (G := G) ≃ f.ker × g.ker where
  toFun x :=
    (⟨(12 : ℕ) • g x, by
      change f ((12 : ℕ) • g x) = 0
      rw [map_nsmul, hfg]
      change (12 : ℕ) • ((19 : ℕ) • (x : G)) = 0
      have hx : (19 : ℕ) • (x : G) = 0 := x.2
      rw [hx, smul_zero]⟩,
     ⟨(12 : ℕ) • f x, by
      change g ((12 : ℕ) • f x) = 0
      rw [map_nsmul, hgf]
      have hx : (19 : ℕ) • (x : G) = 0 := x.2
      rw [hx, smul_zero]⟩)
  invFun z := ⟨(z.1 : G) + (z.2 : G), by
    change (19 : ℕ) • ((z.1 : G) + (z.2 : G)) = 0
    rw [smul_add, kernel_killed_nineteen f g hgf z.1.2,
      kernel_killed_nineteen g f hfg z.2.2, add_zero]⟩
  left_inv x := by
    apply Subtype.ext
    change (12 : ℕ) • g (x : G) + (12 : ℕ) • f (x : G) = x
    rw [← smul_add, add_comm (g (x : G)), hsum, smul_smul]
    exact reduce_ninety_six x.2
  right_inv z := by
    have hu : f (z.1 : G) = 0 := z.1.2
    have hv : g (z.2 : G) = 0 := z.2.2
    apply Prod.ext
    · apply Subtype.ext
      change (12 : ℕ) • g ((z.1 : G) + (z.2 : G)) = z.1
      have hz : g (z.1 : G) = (8 : ℕ) • (z.1 : G) := by
        have h := hsum (z.1 : G)
        rw [hu, zero_add] at h
        exact h
      rw [map_add, hv, add_zero, hz, smul_smul]
      exact reduce_ninety_six (kernel_killed_nineteen f g hgf z.1.2)
    · apply Subtype.ext
      change (12 : ℕ) • f ((z.1 : G) + (z.2 : G)) = z.2
      have hz : f (z.2 : G) = (8 : ℕ) • (z.2 : G) := by
        have h := hsum (z.2 : G)
        rw [hv, add_zero] at h
        exact h
      rw [map_add, hu, zero_add, hz, smul_smul]
      exact reduce_ninety_six (kernel_killed_nineteen g f hfg z.2.2)

def nineteenTorsionEquivFullTorsion
    (hc : Nat.card (CommGroup.torsion (Multiplicative G)) = 19) :
    nineteenTorsion (G := G) ≃ CommGroup.torsion (Multiplicative G) where
  toFun x := ⟨Multiplicative.ofAdd (x : G), by
    rw [CommGroup.mem_torsion]
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨19, by decide, ?_⟩
    change Multiplicative.ofAdd ((19 : ℕ) • (x : G)) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd x.2⟩
  invFun x := ⟨Multiplicative.toAdd (x : Multiplicative G), by
    have hx := pow_card_eq_one' (x := x)
    rw [hc] at hx
    have h := congrArg (fun z : CommGroup.torsion (Multiplicative G) =>
      Multiplicative.toAdd (z : Multiplicative G)) hx
    exact h⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem kernel_card_product
    (hf : Finite (CommGroup.torsion (Multiplicative G)))
    (hc : Nat.card (CommGroup.torsion (Multiplicative G)) = 19)
    (f g : G →+ G)
    (hfg : ∀ x, f (g x) = (19 : ℕ) • x)
    (hgf : ∀ x, g (f x) = (19 : ℕ) • x)
    (hsum : ∀ x, f x + g x = (8 : ℕ) • x) :
    Finite f.ker ∧ Finite g.ker ∧ Nat.card f.ker * Nat.card g.ker = 19 := by
  letI := hf
  let e := (kernelProductEquiv f g hfg hgf hsum).symm.trans
    (nineteenTorsionEquivFullTorsion hc)
  letI : Finite (f.ker × g.ker) := Finite.of_equiv _ e.symm
  letI : Finite f.ker := Finite.of_injective (fun x : f.ker => (x, (0 : g.ker)))
    (fun _ _ h => congrArg Prod.fst h)
  letI : Finite g.ker := Finite.of_injective (fun x : g.ker => ((0 : f.ker), x))
    (fun _ _ h => congrArg Prod.snd h)
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [← Nat.card_prod, Nat.card_congr e, hc]

theorem kernel_card_dichotomy
    (hf : Finite (CommGroup.torsion (Multiplicative G)))
    (hc : Nat.card (CommGroup.torsion (Multiplicative G)) = 19)
    (f g : G →+ G)
    (hfg : ∀ x, f (g x) = (19 : ℕ) • x)
    (hgf : ∀ x, g (f x) = (19 : ℕ) • x)
    (hsum : ∀ x, f x + g x = (8 : ℕ) • x) :
    (Nat.card f.ker = 19 ∧ Nat.card g.ker = 1) ∨
      (Nat.card f.ker = 1 ∧ Nat.card g.ker = 19) := by
  obtain ⟨_, _, h⟩ := kernel_card_product hf hc f g hfg hgf hsum
  have hp : Nat.Prime 19 := by decide
  have hd : Nat.card f.ker ∣ 19 := ⟨Nat.card g.ker, h.symm⟩
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h19
  · exact Or.inr ⟨h1, by simpa only [h1, one_mul] using h⟩
  · apply Or.inl
    refine ⟨h19, ?_⟩
    rw [h19] at h
    omega

end MazurTransfer.NineteenNormRationalKernelDecomposition
#print axioms MazurTransfer.NineteenNormRationalKernelDecomposition.kernel_card_product
#print axioms MazurTransfer.NineteenNormRationalKernelDecomposition.kernel_card_dichotomy

universe u
theorem solution
    (G : Type u) [AddCommGroup G]
    (ht : Finite (CommGroup.torsion (Multiplicative G)))
    (hc : Nat.card (CommGroup.torsion (Multiplicative G)) = 19)
    (f g : G →+ G)
    (hfg : ∀ x, f (g x) = (19 : ℕ) • x)
    (hgf : ∀ x, g (f x) = (19 : ℕ) • x)
    (hsum : ∀ x, f x + g x = (8 : ℕ) • x) :
    Finite f.ker ∧ Finite g.ker ∧ Nat.card f.ker * Nat.card g.ker = 19 ∧
      ((Nat.card f.ker = 19 ∧ Nat.card g.ker = 1) ∨
        (Nat.card f.ker = 1 ∧ Nat.card g.ker = 19)) := by
  obtain ⟨hf, hg, hp⟩ := MazurTransfer.NineteenNormRationalKernelDecomposition.kernel_card_product
    ht hc f g hfg hgf hsum
  exact ⟨hf, hg, hp, MazurTransfer.NineteenNormRationalKernelDecomposition.kernel_card_dichotomy
    ht hc f g hfg hgf hsum⟩
#print axioms solution
