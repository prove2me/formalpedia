-- Prove2me | solution 1 for ModernConvex.PathFollowing.reduced_system_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:56:25.442513+00:00
-- url     : https://prove2.me/submissions/89836873-b07b-4230-ba08-c8b858faca41

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

open ModernConvex.PathFollowing

theorem g70mc2_core {k : ℕ} (x s : Fin k → ℝ) (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i)
    (D E : Matrix (Fin k) (Fin k) ℝ) (hE : E.IsHermitian) (htr : (D * E).trace = 0)
    (heq : D * diagonal s + diagonal x * E + E * diagonal x + diagonal s * D = 0) :
    D = 0 ∧ E = 0 := by
  have hent : ∀ i j, E i j = -((s i + s j) / (x i + x j)) * D i j := by
    intro i j
    have := congrFun (congrFun heq i) j
    simp only [Matrix.add_apply, mul_diagonal, diagonal_mul, Matrix.zero_apply] at this
    have hpos : 0 < x i + x j := add_pos (hx i) (hx j)
    field_simp
    linarith
  have hEs : ∀ i j, E j i = E i j := fun i j => by
    have := congrFun (congrFun hE.eq i) j
    simpa using this
  have hterm : ∀ i j, D i j * E j i = -((s i + s j) / (x i + x j)) * D i j ^ 2 := by
    intro i j; rw [hEs, hent]; ring
  have hc : ∀ i j, 0 < (s i + s j) / (x i + x j) :=
    fun i j => div_pos (add_pos (hs i) (hs j)) (add_pos (hx i) (hx j))
  have htr' : ∑ i, ∑ j, D i j * E j i = 0 := by
    rw [← htr]; simp [trace, mul_apply]
  simp_rw [hterm] at htr'
  have hD : ∀ i j, D i j = 0 := by
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => Finset.sum_nonpos fun j _ => by
      have := hc i j; nlinarith [sq_nonneg (D i j)])).mp htr' i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => by
      have := hc i j; nlinarith [sq_nonneg (D i j)])).mp h1 j (Finset.mem_univ _)
    have := hc i j
    have h3 : D i j ^ 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · linarith
      · exact h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
  refine ⟨Matrix.ext fun i j => hD i j, Matrix.ext fun i j => ?_⟩
  rw [hent, hD]; simp

def g70mc2_Sym (k : ℕ) : Submodule ℝ (Matrix (Fin k) (Fin k) ℝ) where
  carrier := {M | M.IsHermitian}
  add_mem' := fun ha hb => IsHermitian.add ha hb
  zero_mem' := isHermitian_zero
  smul_mem' := fun c M hM => by
    show (c • M)ᴴ = c • M
    rw [conjTranspose_smul, hM.eq, star_trivial]

noncomputable def g70mc2_B (k : ℕ) : LinearMap.BilinForm ℝ (g70mc2_Sym k) :=
  LinearMap.mk₂ ℝ (fun F G => ((F : Matrix (Fin k) (Fin k) ℝ) * G).trace)
    (fun a b c => by simp [add_mul, trace_add])
    (fun c a b => by simp [trace_smul])
    (fun a b c => by simp [mul_add, trace_add])
    (fun c a b => by simp [trace_smul])

theorem g70mc2_B_apply {k : ℕ} (F G : g70mc2_Sym k) :
    g70mc2_B k F G = ((F : Matrix (Fin k) (Fin k) ℝ) * G).trace := rfl

theorem g70mc2_ker {k : ℕ} : LinearMap.ker (g70mc2_B k) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  rw [LinearMap.mem_ker] at hF
  have h := LinearMap.congr_fun hF F
  rw [LinearMap.zero_apply, g70mc2_B_apply] at h
  have hsym : ∀ i j, (F : Matrix (Fin k) (Fin k) ℝ) j i = (F : Matrix (Fin k) (Fin k) ℝ) i j :=
    fun i j => by have := congrFun (congrFun F.2.eq i) j; simpa using this
  have h2 : ∑ i, ∑ j, (F : Matrix (Fin k) (Fin k) ℝ) i j ^ 2 = 0 := by
    rw [← h]; simp [trace, mul_apply, hsym, sq]
  have h3 : ∀ i j, (F : Matrix (Fin k) (Fin k) ℝ) i j = 0 := by
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
      sq_nonneg _)).mp h2 i (Finset.mem_univ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp h1 j (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  exact Subtype.ext (Matrix.ext h3)

theorem g70mc2_aux (U W : Type*) [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (h : Module.finrank ℝ U = Module.finrank ℝ W) (f : U →ₗ[ℝ] W) (hf : Function.Injective f) :
    Function.Surjective f :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mp hf

theorem g70mc2_exists {k : ℕ} (P : SDPPair k) (x s : Fin k → ℝ) (hx : ∀ i, 0 < x i)
    (hs : ∀ i, 0 < s i) (R : Matrix (Fin k) (Fin k) ℝ) (hR : R.IsHermitian) :
    ∃ D E : Matrix (Fin k) (Fin k) ℝ, D ∈ P.L ∧ E ∈ orthSym P.L ∧
      D * diagonal s + diagonal x * E + E * diagonal x + diagonal s * D = R := by
  set V := g70mc2_Sym k
  let Lv : Submodule ℝ V := P.L.comap V.subtype
  let Lp : Submodule ℝ V := (g70mc2_B k).orthogonal Lv
  let Φ : (Lv × Lp) →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ :=
    { toFun := fun p => ((p.1 : V) : Matrix (Fin k) (Fin k) ℝ) * diagonal s +
        diagonal x * ((p.2 : V) : Matrix (Fin k) (Fin k) ℝ) +
        ((p.2 : V) : Matrix (Fin k) (Fin k) ℝ) * diagonal x +
        diagonal s * ((p.1 : V) : Matrix (Fin k) (Fin k) ℝ)
      map_add' := fun a b => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_mul, mul_add]; abel
      map_smul' := fun c a => by
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Matrix.smul_mul,
          Matrix.mul_smul, smul_add, RingHom.id_apply] }
  have hΦ : ∀ p, Φ p ∈ V := by
    intro p
    have h1 := (p.1 : V).2
    have h2 := (p.2 : V).2
    change IsHermitian _ at h1 h2 ⊢
    unfold IsHermitian at *
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, conjTranspose_add, conjTranspose_mul, h1, h2,
      diagonal_conjTranspose, star_trivial]
    abel
  let T : (Lv × Lp) →ₗ[ℝ] V := Φ.codRestrict V hΦ
  have hinj : Function.Injective T := by
    intro a b hab
    rw [← sub_eq_zero]
    have hp : T (a - b) = 0 := by rw [LinearMap.map_sub T a b, hab, sub_self]
    set p := a - b
    have hp' : Φ p = 0 := congrArg Subtype.val hp
    have hE : ((p.2 : V) : Matrix (Fin k) (Fin k) ℝ).IsHermitian := (p.2 : V).2
    have htr : (((p.1 : V) : Matrix (Fin k) (Fin k) ℝ) * ((p.2 : V) : Matrix (Fin k) (Fin k) ℝ)).trace = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp p.2.2) _ p.1.2
    obtain ⟨h1, h2⟩ := g70mc2_core x s hx hs _ _ hE htr hp'
    ext <;> simp [h1, h2]
  have : Module.Free ℝ Lv := Module.Free.of_divisionRing ℝ Lv
  have : Module.Free ℝ Lp := Module.Free.of_divisionRing ℝ Lp
  have hdim : Module.finrank ℝ (Lv × Lp) = Module.finrank ℝ V := by
    rw [Module.finrank_prod]
    have := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := g70mc2_B k) Lv
    rw [g70mc2_ker, inf_bot_eq, finrank_bot, add_zero] at this
    exact this
  have hsurj : Function.Surjective T :=
    g70mc2_aux (Lv × Lp) V hdim T hinj
  obtain ⟨p, hp⟩ := hsurj ⟨R, hR⟩
  refine ⟨(p.1 : V), (p.2 : V), p.1.2, ⟨(p.2 : V).2, fun X hX => ?_⟩, congrArg Subtype.val hp⟩
  have hXV : X ∈ V := P.L_sym X hX
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp p.2.2) ⟨X, hXV⟩ hX

theorem solution {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ)
    (x s : Fin k → ℝ) (h : P.ReducedSituation κ χ x s) :
    ∃! d : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ,
      P.IsReducedDirection (diagonal x) (diagonal s) (muPlus k χ) d.1 d.2 := by
  set R : Matrix (Fin k) (Fin k) ℝ :=
    (2 * muPlus k χ) • (1 : Matrix (Fin k) (Fin k) ℝ) - (2 : ℝ) • (diagonal x * diagonal s)
  have hRd : R = diagonal fun i => 2 * muPlus k χ - 2 * (x i * s i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [R]
    · simp [R, hij, one_apply_ne hij]
  have hR : R.IsHermitian := by rw [hRd]; exact isHermitian_diagonal _
  obtain ⟨D, E, hD, hE, heq⟩ := g70mc2_exists P x s h.x_pos h.s_pos R hR
  refine ⟨(D, E), ⟨hD, hE, ?_⟩, ?_⟩
  · exact heq
  · rintro ⟨D', E'⟩ ⟨hD', hE', heq'⟩
    have hdiff := g70mc2_core x s h.x_pos h.s_pos (D' - D) (E' - E) (hE'.1.sub hE.1)
      (by
        rw [mul_sub, trace_sub, hE'.2 _ (P.L.sub_mem hD' hD), hE.2 _ (P.L.sub_mem hD' hD),
          sub_self])
      (by
        have e : (D' - D) * diagonal s + diagonal x * (E' - E) + (E' - E) * diagonal x +
            diagonal s * (D' - D) =
            (D' * diagonal s + diagonal x * E' + E' * diagonal x + diagonal s * D') -
            (D * diagonal s + diagonal x * E + E * diagonal x + diagonal s * D) := by
          simp only [sub_mul, mul_sub]; abel
        rw [e]
        have e2 : D * diagonal s + diagonal x * E + E * diagonal x + diagonal s * D =
            D * diagonal s + diagonal x * E + E * diagonal x + diagonal s * D := rfl
        simp only at heq'
        rw [heq', heq, sub_self])
    obtain ⟨h1, h2⟩ := hdiff
    simp only [Prod.mk.injEq]
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
