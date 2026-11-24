-- Prove2me | solution 1 for GlobalTheory.exists_mul_eq_polynomial_weierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:52.203637+00:00
-- url     : https://prove2.me/submissions/c7e67a7b-c945-4f67-a9e0-0f4dffef8bde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Theorems.Thm_GlobalTheory_exists_eq_polynomial_weierstrassP
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Polynomial
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {f : ℂ → ℂ} (hf : Meromorphic f)
    (hp : ∀ z, ∀ l ∈ L.lattice, f (z + l) = f z) (hev : ∀ z, f (-z) = f z) :
    ∃ A D : ℂ[X], D.Monic ∧ ∀ z ∉ L.lattice, f z * D.eval (℘[L] z) = A.eval (℘[L] z) := by
  classical
  have hK : IsCompact (closure (ZSpan.fundamentalDomain L.basis)) :=
    (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure
  have hBc : IsClosed {z | ¬ AnalyticAt ℂ f z} := (isOpen_analyticAt ℂ f).isClosed_compl
  have hfin : (closure (ZSpan.fundamentalDomain L.basis) ∩ {z | ¬ AnalyticAt ℂ f z}).Finite := by
    refine (hK.inter_right hBc).finite ?_
    rw [isDiscrete_iff_nhdsNE]
    intro x _
    rw [Filter.inf_principal_eq_bot]
    filter_upwards [(hf x).eventually_analyticAt] with y hy
    exact fun hyS => hyS.2 hy
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, ∀ a, a ∈ S ↔
      a ∈ closure (ZSpan.fundamentalDomain L.basis) ∩ {z | ¬ AnalyticAt ℂ f z} :=
    ⟨hfin.toFinset, fun a => hfin.mem_toFinset⟩
  choose n hn using hf
  let D : ℂ[X] := ∏ a ∈ S, (X - C (℘[L] a)) ^ (n a + 1)
  have hD : D.Monic := monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C _).pow _
  let g : ℂ → ℂ := fun z => f z * D.eval (℘[L] z)
  have h℘d : ∀ z ∉ L.lattice, DifferentiableAt ℂ ℘[L] z :=
    fun z hz => (hasDerivAt_weierstrassP L hz).differentiableAt
  have hPd : ∀ (p : ℂ[X]) (z : ℂ), z ∉ L.lattice → DifferentiableAt ℂ (fun w => p.eval (℘[L] w)) z :=
    fun p z hz => (p.differentiableAt (x := ℘[L] z)).comp z (h℘d z hz)
  have hPm : ∀ p : ℂ[X], MeromorphicAt (fun w => p.eval (℘[L] w)) 0 := by
    intro p
    have h℘m := L.meromorphic_weierstrassP 0
    refine Polynomial.induction_on (motive := fun p => MeromorphicAt (fun w => p.eval (℘[L] w)) 0)
      p ?_ ?_ ?_
    · intro a
      simp
    · intro p q hp hq
      simp only [eval_add]
      exact hp.add hq
    · intro k a _
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      fun_prop
  have hgp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z := by
    intro z l hl
    have h℘ : ℘[L] (z + l) = ℘[L] z := L.weierstrassP_add_coe z ⟨l, hl⟩
    simp only [g, hp z l hl, h℘]
  have hgev : ∀ z, g (-z) = g z := fun z => by simp only [g, hev, L.weierstrassP_neg]
  have hgS : ∀ a ∈ S, a ∉ L.lattice → DifferentiableAt ℂ g a := by
    intro a ha hal
    have hψ : DifferentiableAt ℂ (dslope ℘[L] a) a := by
      have hs : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 a := L.isClosed_lattice.isOpen_compl.mem_nhds hal
      exact ((Complex.differentiableOn_dslope hs).mpr L.differentiableOn_weierstrassP).differentiableAt hs
    have hDR : D = (X - C (℘[L] a)) ^ (n a + 1) * ∏ b ∈ S.erase a, (X - C (℘[L] b)) ^ (n b + 1) :=
      (Finset.mul_prod_erase S (fun b => (X - C (℘[L] b)) ^ (n b + 1)) ha).symm
    have hfun : g = fun w => (w - a) * ((w - a) ^ (n a) • f w) * (dslope ℘[L] a w) ^ (n a + 1) *
        (∏ b ∈ S.erase a, (X - C (℘[L] b)) ^ (n b + 1)).eval (℘[L] w) := by
      funext w
      have e := sub_smul_dslope ℘[L] a w
      rw [smul_eq_mul] at e
      simp only [g, hDR, eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]
      rw [← e, mul_pow]
      ring
    rw [hfun]
    have h1 := (hn a).differentiableAt
    have h3 := hPd (∏ b ∈ S.erase a, (X - C (℘[L] b)) ^ (n b + 1)) a hal
    have h0 : DifferentiableAt ℂ (fun w : ℂ => w - a) a := differentiableAt_id.sub_const a
    exact ((h0.mul h1).mul (hψ.pow _)).mul h3
  have hgd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z := by
    intro z hz
    by_cases hfa : AnalyticAt ℂ f z
    · exact hfa.differentiableAt.mul (hPd D z hz)
    obtain ⟨a, l, hlL, rfl, haK⟩ : ∃ a l, l ∈ L.lattice ∧ z = a + l ∧
        a ∈ closure (ZSpan.fundamentalDomain L.basis) :=
      ⟨ZSpan.fract L.basis z, ZSpan.floor L.basis z,
        by rw [L.lattice_eq_span_range_basis]; exact (ZSpan.floor L.basis z).2,
        by rw [ZSpan.fract_apply]; ring,
        subset_closure (ZSpan.fract_mem_fundamentalDomain L.basis z)⟩
    have hal : a ∉ L.lattice := fun h => hz (L.lattice.add_mem h hlL)
    have haB : ¬ AnalyticAt ℂ f a := by
      intro hfa'
      apply hfa
      have htf : (fun w => f (w - l)) = f := funext fun w => by
        have := hp (w - l) l hlL
        rw [sub_add_cancel] at this
        exact this.symm
      rw [← htf]
      have h2 : AnalyticAt ℂ (fun w : ℂ => w - l) (a + l) := by fun_prop
      exact hfa'.comp_of_eq h2 (by simp)
    have haS : a ∈ S := (hS a).mpr ⟨haK, haB⟩
    have hga := hgS a haS hal
    have htr : g = fun w => g (w - l) := funext fun w => by
      have := hgp (w - l) l hlL
      rw [sub_add_cancel] at this
      exact this
    rw [htr]
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w - l) (a + l) := differentiableAt_id.sub_const l
    have h3 : DifferentiableAt ℂ g ((fun w : ℂ => w - l) (a + l)) := by simpa using hga
    exact DifferentiableAt.comp (g := g) (f := fun w : ℂ => w - l) (a + l) h3 h2
  have hg0 : MeromorphicAt g 0 := (show MeromorphicAt f 0 from ⟨n 0, hn 0⟩).mul (hPm D)
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L hg0 hgd hgp hgev
  exact ⟨A, D, hD, hA⟩
end GlobalTheory
