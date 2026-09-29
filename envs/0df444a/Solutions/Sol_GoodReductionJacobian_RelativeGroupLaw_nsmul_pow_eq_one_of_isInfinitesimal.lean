-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d6d415ab-0ba5-543f-8974-c57fefaa9243

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_MvFormalGroup_iterate_nilMul_sub_natCast_mul_mem_pow
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace KatzRGAux

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmul_add (G : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (m k : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (m + k) x = G.mul t (G.nsmul t m x) (G.nsmul t k x) := by
  induction k with
  | zero => rw [Nat.add_zero, G.nsmul_zero, G.mul_one]
  | succ k ih => rw [Nat.add_succ, G.nsmul_succ, G.nsmul_succ, ih, G.mul_assoc]

theorem nsmul_mul (G : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (m k : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (m * k) x = G.nsmul t k (G.nsmul t m x) := by
  induction k with
  | zero => rw [Nat.mul_zero, G.nsmul_zero, G.nsmul_zero]
  | succ k ih => rw [Nat.mul_succ, nsmul_add, ih, G.nsmul_succ]

theorem eq_one_of_mul_self (G : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (a : SchemeHomOver t f) (h : G.mul t a a = a) : a = G.one t := by
  calc a = G.mul t (G.one t) a := (G.one_mul t a).symm
    _ = G.mul t (G.mul t (G.inv t a) a) a := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t a) (G.mul t a a) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t a) a := by rw [h]
    _ = G.one t := G.inv_mul_cancel t a

end KatzRGAux

theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {g : ℕ} (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    {B' : Type} [CommRing B'] [Algebra B B'] (N : ℕ) (hN : (N : B') = 0)
    (J : Ideal B') (μ : ℕ) (hJ : J ^ (μ + 1) = ⊥)
    (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f) (hP : L.IsInfinitesimal J P) :
    L.nsmul (Scheme.specOver (𝒪 := B) B') (N ^ μ) P = L.one (Scheme.specOver (𝒪 := B) B') := by
  classical
  obtain ⟨hnat, hkey⟩ := hθ
  obtain ⟨hinto, hinj, honto, hhom⟩ := hkey B' J μ hJ

  have hclos : ∀ u v : Fin g → B', (∀ i, u i ∈ J) → (∀ i, v i ∈ J) → ∀ i, F.nilMul μ u v i ∈ J := by
    intro u v hu hv i
    have hsum : ∀ x : Fin g ⊕ Fin g, Sum.elim u v x ∈ J := by
      rintro (x | x)
      · exact hu x
      · exact hv x
    exact (MvFormalGroup.nilEval_subst_of_mem J μ hJ (Sum.elim u v) hsum F.toPowerSeries F.constantCoeff_eq_zero
      (0 : MvPowerSeries (Fin g) B)).1 i
  have hzero : ∀ i, (0 : Fin g → B') i ∈ J := fun _ => J.zero_mem
  have hθ0 : θ B' (0 : Fin g → B') = L.one (Scheme.specOver (𝒪 := B) B') := by
    have h00 : F.nilMul μ (0 : Fin g → B') 0 = 0 := by
      funext i

      have hb : ((⊥ : Ideal B') ^ (μ + 1)) = ⊥ := by
        rw [← Ideal.zero_eq_bot, zero_pow (Nat.succ_ne_zero μ)]
      have := (MvFormalGroup.nilEval_subst_of_mem (⊥ : Ideal B') μ hb (Sum.elim (0 : Fin g → B') 0)
        (by rintro (x | x) <;> simp) F.toPowerSeries F.constantCoeff_eq_zero (0 : MvPowerSeries (Fin g) B)).1 i
      show MvFormalGroup.nilEval μ (F.toPowerSeries i) (Sum.elim (0 : Fin g → B') 0) = 0
      have e0 : (Sum.elim (0 : Fin g → B') (0 : Fin g → B')) = 0 := by
        funext x; rcases x with x | x <;> rfl
      rw [e0]; simpa using this
    have h := hhom (0 : Fin g → B') 0 hzero hzero
    rw [h00] at h
    exact KatzRGAux.eq_one_of_mul_self L (Scheme.specOver (𝒪 := B) B') _ h.symm

  have hiterJ : ∀ s : Fin g → B', (∀ i, s i ∈ J) → ∀ m i, ((fun u : Fin g → B' => F.nilMul μ u s)^[m] (0 : Fin g → B')) i ∈ J := by
    intro s hs m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
        intro i
        rw [Function.iterate_succ_apply']
        exact hclos _ _ ih hs i
  have hA : ∀ s : Fin g → B', (∀ i, s i ∈ J) → ∀ m,
      L.nsmul (Scheme.specOver (𝒪 := B) B') m (θ B' s) = θ B' ((fun u : Fin g → B' => F.nilMul μ u s)^[m] (0 : Fin g → B')) := by
    intro s hs m
    induction m with
    | zero => rw [L.nsmul_zero, Function.iterate_zero_apply, hθ0]
    | succ m ih =>
        rw [L.nsmul_succ, ih, Function.iterate_succ_apply', hhom _ _ (hiterJ s hs m) hs]

  obtain ⟨s, hsJ, hsP⟩ := honto P hP
  have hC : ∀ j, ∃ sj : Fin g → B', (∀ i, sj i ∈ J ^ (j + 1)) ∧ θ B' sj = L.nsmul (Scheme.specOver (𝒪 := B) B') (N ^ j) P := by
    intro j
    induction j with
    | zero => exact ⟨s, fun i => by simpa using hsJ i, by rw [pow_zero, L.nsmul_one_apply, hsP]⟩
    | succ j ih =>
        obtain ⟨sj, hsj, hθsj⟩ := ih
        have hsjJ : ∀ i, sj i ∈ J := fun i => Ideal.pow_le_self (Nat.succ_ne_zero j) (hsj i)
        refine ⟨(fun u : Fin g → B' => F.nilMul μ u sj)^[N] (0 : Fin g → B'), fun i => ?_, ?_⟩
        · have hfg := MvFormalGroup.iterate_nilMul_sub_natCast_mul_mem_pow F J μ hJ (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
            sj hsj N i
          rw [hN, zero_mul, sub_zero] at hfg
          exact hfg
        · rw [← hA sj hsjJ N, hθsj, ← KatzRGAux.nsmul_mul, pow_succ]
  obtain ⟨sμ, hsμ, hθsμ⟩ := hC μ
  have hs0 : sμ = 0 := by
    funext i
    have := hsμ i
    rw [hJ, Submodule.mem_bot] at this
    exact this
  rw [← hθsμ, hs0, hθ0]

end S_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal (solution)
