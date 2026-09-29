-- Prove2me | solution 1 for MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebung_homothety_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b7dec7b4-852e-5079-8a56-3649382e203f

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebung_homothety_add

set_option autoImplicit false

noncomputable section

open MvFormalGroup MvFormalGroup.CartierModule

universe u

namespace P2mKcVBasis

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
variable {Φ : MvFormalGroup d R} [Φ.IsComm]

def expansion (f : Fin d → CartierModule p Φ) (N : ℕ) (c : Fin N → Fin d → R)
    (h : CartierModule p Φ) : CartierModule p Φ :=
  (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m]
      (∑ i : Fin d, homothety (c m i) (f i))) +
    (⇑(verschiebung (p := p) (Φ := Φ)))^[N] h

theorem expansion_zero (f : Fin d → CartierModule p Φ) (c : Fin 0 → Fin d → R)
    (h : CartierModule p Φ) : expansion f 0 c h = h := by
  simp [expansion]

theorem expansion_succ (f : Fin d → CartierModule p Φ) (N : ℕ) (c : Fin (N + 1) → Fin d → R)
    (h : CartierModule p Φ) :
    expansion f (N + 1) c h =
      (∑ i : Fin d, homothety (c 0 i) (f i)) + verschiebung (expansion f N (Fin.tail c) h) := by
  unfold expansion
  rw [Fin.sum_univ_succ, map_add, map_sum, add_assoc]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Fin.val_succ, Function.iterate_succ_apply']
    rfl
  · rw [Function.iterate_succ_apply']

def tanMat (f : Fin d → CartierModule p Φ) : Matrix (Fin d) (Fin d) R :=
  Matrix.of fun i j => tangent (f i) j

omit [CharP R p] in
theorem tangent_sum_homothety (f : Fin d → CartierModule p Φ) (c : Fin d → R) :
    tangent (∑ i : Fin d, homothety (c i) (f i)) = Matrix.vecMul c (tanMat f) := by
  rw [map_sum]
  funext j
  rw [Finset.sum_apply, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tangent_homothety, Pi.smul_apply, smul_eq_mul]
  rfl

theorem tangent_verschiebung_iterate (n : ℕ) (h : CartierModule p Φ) :
    tangent ((⇑(verschiebung (p := p) (Φ := Φ)))^[n + 1] h) = 0 := by
  rw [Function.iterate_succ_apply']
  exact tangent_verschiebung _

theorem tangent_expansion_succ (f : Fin d → CartierModule p Φ) (N : ℕ)
    (c : Fin (N + 1) → Fin d → R) (h : CartierModule p Φ) :
    tangent (expansion f (N + 1) c h) = Matrix.vecMul (c 0) (tanMat f) := by
  rw [expansion_succ, map_add, tangent_sum_homothety, tangent_verschiebung, add_zero]

theorem exists_expansion (f : Fin d → CartierModule p Φ) (hf : IsUnit (tanMat f).det) :
    ∀ (N : ℕ) (g : CartierModule p Φ), ∃ (c : Fin N → Fin d → R) (h : CartierModule p Φ),
      g = expansion f N c h := by
  intro N
  induction N with
  | zero => intro g; exact ⟨Fin.elim0, g, (expansion_zero f _ g).symm⟩
  | succ N ih =>
    intro g

    set c₀ : Fin d → R := Matrix.vecMul (tangent g) (tanMat f)⁻¹ with hc₀
    have hT : Matrix.vecMul c₀ (tanMat f) = tangent g := by
      rw [hc₀, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hf, Matrix.vecMul_one]
    set g₀ : CartierModule p Φ := ∑ i : Fin d, homothety (c₀ i) (f i) with hg₀
    have htan : tangent (g - g₀) = 0 := by
      rw [map_sub, hg₀, tangent_sum_homothety, hT, sub_self]
    obtain ⟨g₁, hg₁⟩ :=
      (MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebung_eq p Φ (g - g₀)).mp htan
    obtain ⟨c, h, hc⟩ := ih g₁
    refine ⟨Fin.cons c₀ c, h, ?_⟩
    rw [expansion_succ, Fin.cons_zero, Fin.tail_cons, ← hc, hg₁, ← hg₀, add_sub_cancel]

theorem expansion_injective (f : Fin d → CartierModule p Φ) (hf : IsUnit (tanMat f).det) :
    ∀ (N : ℕ) (c c' : Fin N → Fin d → R) (h h' : CartierModule p Φ),
      expansion f N c h = expansion f N c' h' → c = c' ∧ h = h' := by
  intro N
  induction N with
  | zero =>
    intro c c' h h' he
    refine ⟨funext fun m => m.elim0, ?_⟩
    rwa [expansion_zero, expansion_zero] at he
  | succ N ih =>
    intro c c' h h' he
    have h0 : c 0 = c' 0 := by
      have ht := congrArg tangent he
      rw [tangent_expansion_succ, tangent_expansion_succ] at ht
      have := congrArg (fun v => Matrix.vecMul v (tanMat f)⁻¹) ht
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hf, Matrix.vecMul_one] using this
    rw [expansion_succ, expansion_succ, h0] at he
    have he' := add_left_cancel he
    obtain ⟨htail, hh⟩ := ih _ _ _ _ (verschiebung_injective he')
    refine ⟨?_, hh⟩
    funext m
    refine Fin.cases ?_ (fun m' => ?_) m
    · exact h0
    · exact congrFun htail m'

end P2mKcVBasis

open P2mKcVBasis in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (f i) j).det)
    (g : MvFormalGroup.CartierModule p Φ) (N : ℕ) :
    ∃! ch : (Fin N → Fin d → R) × MvFormalGroup.CartierModule p Φ,
      g = (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[m]
              (∑ i : Fin d, MvFormalGroup.CartierModule.homothety (ch.1 m i) (f i))) +
          (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] ch.2 := by
  obtain ⟨c, h, hc⟩ := exists_expansion f hf N g
  refine ⟨(c, h), hc, ?_⟩
  rintro ⟨c', h'⟩ hc'
  have := expansion_injective f hf N c' c h' h (hc'.symm.trans hc)
  rw [Prod.mk.injEq]
  exact this

end

end S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebung_homothety_add
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebung_homothety_add (solution)
