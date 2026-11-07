-- Prove2me | solution 1 for NaturalProofs.level_hybrid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:57.868307+00:00
-- url     : https://prove2.me/submissions/1cea8289-0441-42ee-8314-2780306c4e9d

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_hybF_succ
public import Theorems.Thm_NaturalProofs_expand_bijective
public import Theorems.Thm_NaturalProofs_hybF_zero
public import Theorems.Thm_NaturalProofs_hybF_top
public import Theorems.Thm_NaturalProofs_multi_sample
public import Theorems.Thm_NaturalProofs_prob_equiv
public import Theorems.Thm_NaturalProofs_prob_fst
public import Theorems.Thm_NaturalProofs_telescope


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
namespace NaturalProofs
theorem _root_.solution {k : ℕ} (hk : 0 < k) (n : ℕ) (hn : 0 < n) (T : BoolFn n → Bool) :
    ∃ i < n, ∃ (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool),
      |prob (fun s => T (prf G k n s)) - prob T| / (n * 2 ^ i) ≤
        |prob (fun u : Bits k => T (hybF G (i + 1) (expand (Function.update c e (G k u))))) -
          prob (fun y : Fin (2 * k) → Bool => T (hybF G (i + 1) (expand (Function.update c e y))))| := by
  let Q : ℕ → ℝ := fun i => prob (fun L : (Fin i → Bool) → Bits k => T (hybF G i L))
  have hQ0 : Q 0 = prob (fun s => T (prf G k n s)) := by
    have key : (fun L : (Fin 0 → Bool) → Bits k => T (hybF G 0 L)) =
        fun L => T (prf G k n (Equiv.funUnique (Fin 0 → Bool) (Bits k) L)) := by
      funext L
      rw [hybF_zero G L (fun j => j.elim0)]
      congr 2
    simp only [Q]
    rw [key]
    exact prob_equiv (Equiv.funUnique (Fin 0 → Bool) (Bits k)) (fun s => T (prf G k n s))
  have hQn : Q n = prob T := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    let φ := (Equiv.arrowCongr (Equiv.refl (Fin n → Bool))
        (Fin.consEquiv (fun _ : Fin (k' + 1) => Bool)).symm).trans
      (Equiv.arrowProdEquivProdArrow (Fin n → Bool) (fun _ => Bool) (fun _ => Fin k' → Bool))
    have : (fun L : (Fin n → Bool) → Bits (k' + 1) => T (hybF G n L)) =
        fun L => (fun p : BoolFn n × ((Fin n → Bool) → Fin k' → Bool) => T p.1) (φ L) := by
      funext L
      simp [hybF_top, φ, firstBit]
    simp only [Q]
    rw [this, prob_equiv φ (fun p : BoolFn n × ((Fin n → Bool) → Fin k' → Bool) => T p.1),
      prob_fst T]
  obtain ⟨i, hi, hstep⟩ := telescope Q n hn
  let F : ((Fin i → Bool) → Fin (2 * k) → Bool) → Bool := fun M => T (hybF G (i + 1) (expand M))
  have hQi : Q i = prob (fun L : (Fin i → Bool) → Bits k => F (fun p => G k (L p))) := by
    simp only [Q, F, ← hybF_succ G i hi]
  have hQi1 : Q (i + 1) = prob F := by
    simp only [Q, F]
    exact (prob_equiv (Equiv.ofBijective _ (expand_bijective k i))
      (fun L : (Fin (i + 1) → Bool) → Bits k => T (hybF G (i + 1) L))).symm
  obtain ⟨e, c, hms⟩ := multi_sample (G k) F
  refine ⟨i, hi, e, c, ?_⟩
  rw [hQ0, hQn, hQi, hQi1] at hstep
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] at hms
  have h2 : (0 : ℝ) < 2 ^ i := by positivity
  calc _ = |prob (fun s => T (prf G k n s)) - prob T| / n / 2 ^ i := by rw [div_div]
    _ ≤ |prob (fun L : (Fin i → Bool) → Bits k => F (fun p => G k (L p))) - prob F| / 2 ^ i :=
        div_le_div_of_nonneg_right hstep h2.le
    _ ≤ _ := hms
end NaturalProofs
