-- Prove2me | solution 1 for GlobalTheory.CharpolyDvd.matrix_charpoly_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:54.57447+00:00
-- url     : https://prove2.me/submissions/aad015fb-3437-438d-8bd6-76dc54bb8f0b

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
open GlobalTheory GlobalTheory.CharpolyDvd
namespace GlobalTheory.CharpolyDvd
theorem _root_.solution {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by
  classical
  by_cases h0 : G = 0
  · subst h0
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · have : M.charpoly = 1 := by
        apply Polynomial.eq_one_of_monic_natDegree_zero M.charpoly_monic
        rw [Matrix.charpoly_natDegree_eq_dim, h]
      rw [this, h, pow_zero]
    · rw [zero_pow h.ne']
      exact dvd_zero _
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  rw [← Polynomial.map_dvd_map' f, Polynomial.map_pow, ← Matrix.charpoly_map]
  set N := M.map f with hNdef
  have hN : aeval N (G.map f) = 0 := by
    rw [aeval_map_algebraMap]
    have := congrArg (AlgHom.mapMatrix (m := ι) (Algebra.ofId K Ω)) hG
    rw [← aeval_algHom_apply, map_zero] at this
    exact this
  have hG0 : G.map f ≠ 0 := Polynomial.map_ne_zero h0
  have hq0 : G.map f ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hG0
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots N.charpoly_monic.ne_zero ?_
  rw [roots_pow, Multiset.le_iff_count]
  intro μ
  rw [Multiset.count_nsmul]
  by_cases hμ : μ ∈ N.charpoly.roots
  · have h1 : μ ∈ spectrum Ω N := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact isRoot_of_mem_roots hμ
    have h2 := spectrum.subset_polynomial_aeval N (G.map f) ⟨μ, h1, rfl⟩
    rw [hN] at h2
    have h3 : (G.map f).eval μ = 0 := by
      by_contra hne
      exact (spectrum.mem_iff.1 h2)
        (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix ι ι Ω)))
    have h4 : 1 ≤ (G.map f).roots.count μ :=
      Multiset.one_le_count_iff_mem.2 ((mem_roots hG0).2 h3)
    calc N.charpoly.roots.count μ ≤ Multiset.card N.charpoly.roots := Multiset.count_le_card _ _
      _ ≤ N.charpoly.natDegree := card_roots' _
      _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim N
      _ ≤ Fintype.card ι * (G.map f).roots.count μ := Nat.le_mul_of_pos_right _ h4
  · rw [Multiset.count_eq_zero.2 hμ]
    exact Nat.zero_le _
end GlobalTheory.CharpolyDvd
