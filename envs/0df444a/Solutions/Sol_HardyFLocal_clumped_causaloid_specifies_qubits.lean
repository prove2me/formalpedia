-- Prove2me | solution 1 for HardyFLocal.clumped_causaloid_specifies_qubits
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:54:27.842311+00:00
-- url     : https://prove2.me/submissions/a81cec5c-b6be-4bc2-9bbb-9c99a2e53328
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HardyCausaloid_Conditional
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_regional_outcome_summability
import Theorems.Thm_HardyFLocal_clumping_respects_f_locality
import Theorems.Thm_HardyFLocal_clumping_computes_probabilities
import Theorems.Thm_HardyFLocal_clump_labels_fiducial_interior
namespace HardyCausaloid
private theorem tsum_pairing {ι B : Type*} [Fintype ι] (v : B → ι → ℝ)
    (hv : Summable v) (x : ι → ℝ) :
    (∑' b, v b ⬝ᵥ x) = (∑' b, v b) ⬝ᵥ x := by
  exact (hasSum_sum fun i (_ : i ∈ Finset.univ) =>
    ((Pi.hasSum.mp hv.hasSum) i).mul_right (x i)).tsum_eq

variable {X : Type*} {Setting : X → Type*} {Outcome : (x : X) → Setting x → Type*}
  [DecidableEq X]

private theorem scalar_outcome_summable (M : Model Setting Outcome)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂) (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.val) (base : ∀ x : O₂, Outcome x.val (F₂ x))
    (s : ∀ x, Label Setting Outcome x) :
    Summable (fun β : ∀ x : O₂, Outcome x.val (F₂ x) =>
      regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β)) s) := by
  classical
  let total (β : ∀ x : O₂, Outcome x.val (F₂ x)) :=
    glue (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β)) s
  let F x := (total base x).1
  have hF β x : (total β x).1 = F x := by
    by_cases hu : x ∈ O₁ ∪ O₂ <;> by_cases ha : x ∈ O₁ <;>
      simp only [F, total, glue, joinLab, labOf, hu, ha, ↓reduceDIte]
  let out (β : ∀ x : O₂, Outcome x.val (F₂ x)) (x : X) : Outcome x (F x) :=
    (hF β x) ▸ (total β x).2
  have labels β x : (⟨F x, out β x⟩ : Label Setting Outcome x) = total β x := by
    refine Sigma.ext ?_ ?_
    · exact (hF β x).symm
    · exact eqRec_heq _ _
  have onTwo β (x : O₂) : total β x.val = ⟨F₂ x, β x⟩ := by
    have ha : x.val ∉ O₁ := fun hx => Finset.disjoint_left.mp hO hx x.property
    have hu := Finset.mem_union_right O₁ x.property
    simp [total, glue, joinLab, labOf, hu, ha]
  have inj : Function.Injective out := by
    intro β γ h
    funext x
    have hl : total β x.val = total γ x.val :=
      (labels β x.val).symm.trans ((congrArg (Sigma.mk (F x.val)) (congrFun h x.val)).trans (labels γ x.val))
    rw [onTwo, onTwo] at hl
    exact eq_of_heq (Sigma.mk.inj_iff.mp hl).2
  have hs := (M.hasSum_prob F).summable.comp_injective inj
  apply hs.congr
  intro β
  change M.prob F (out β) = M.P (total β)
  change M.P (fun x => ⟨F x, out β x⟩) = _
  rw [show (fun x => (⟨F x, out β x⟩ : Label Setting Outcome x)) = total β from funext (labels β)]

end HardyCausaloid
namespace HardyCausaloid

private theorem states_separate {ι S : Type*} [Fintype ι] (p : S → ι → ℝ)
    (hs : Submodule.span ℝ (Set.range p) = ⊤) {u v : ι → ℝ}
    (h : ∀ s, u ⬝ᵥ p s = v ⬝ᵥ p s) : u = v := by
  apply dotProduct_eq
  intro x
  have hx : x ∈ Submodule.span ℝ (Set.range p) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨s, rfl⟩ := hx; exact h s
  | zero => simp
  | add x y _ _ hx hy => simp only [dotProduct_add, hx, hy]
  | smul c x _ hx => simp only [dotProduct_smul, hx]

private theorem length_pos {ι : Type*} [Fintype ι] {v : ι → ℝ} (h : v ≠ 0) :
    0 < euclidLength v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  apply Real.sqrt_pos.mpr
  exact (sq_pos_of_ne_zero hi).trans_le (Finset.single_le_sum
    (f := fun j => (v j)^2) (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

private theorem length_smul {ι : Type*} [Fintype ι] (v : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    euclidLength (c • v) = c * euclidLength v := by
  simp only [euclidLength, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

end HardyCausaloid

open HardyFLocal HardyCausaloid

theorem solution {m n : ℕ} (ρ : GlobalMat m n) (hρ : IsDensity ρ)
    (M : Model (Setting m n) (Outcome m n)) (hM : IsLatticeModel ρ M) (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L) :
    let C := actualCausaloid S L
    (∀ (O : Finset (X m n)) (α : Lab (Setting m n) (Outcome m n) O)
        (s : ∀ x, Label (Setting m n) (Outcome m n) x),
      regionTable M O α s = C.r O α ⬝ᵥ C.state M O s) ∧
    (∀ O : Finset (X m n), Interior O → Fiducial (regionTable M O) (C.fidSet O)) ∧
    (∀ O₁ O₂ : Finset (X m n), Disjoint O₁ O₂ →
      ∀ (α₁ : Lab (Setting m n) (Outcome m n) O₁) (F₂ : ∀ x : O₂, Setting m n x.1)
        (Y₂ : ∀ x : O₂, Outcome m n x.1 (F₂ x)),
        Summable (fun β₂ : (∀ x : O₂, Outcome m n x.1 (F₂ x)) =>
          C.r (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂))) ∧
        (∀ s, Summable (fun β₂ : (∀ x : O₂, Outcome m n x.1 (F₂ x)) =>
          regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂)) s)) ∧
        (∀ s, condNum M α₁ F₂ Y₂ s = condA C α₁ F₂ Y₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s ∧
          condDen M α₁ F₂ s = condB C α₁ F₂ ⬝ᵥ C.state M (O₁ ∪ O₂) s) ∧
        (∀ c : ℝ, condA C α₁ F₂ Y₂ = c • condB C α₁ F₂ → IsCondValue M α₁ F₂ Y₂ c ∧
          (condB C α₁ F₂ ≠ 0 → IsCondValue M α₁ F₂ Y₂
            (euclidLength (condA C α₁ F₂ Y₂) / euclidLength (condB C α₁ F₂)))) ∧
        (Interior (O₁ ∪ O₂) →
          (CondWellDefined M α₁ F₂ Y₂ ↔ ∃ c : ℝ, condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
          (∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c → condA C α₁ F₂ Y₂ = c • condB C α₁ F₂) ∧
          (condB C α₁ F₂ ≠ 0 → ∀ c : ℝ, IsCondValue M α₁ F₂ Y₂ c →
            c = euclidLength (condA C α₁ F₂ Y₂) / euclidLength (condB C α₁ F₂)) ∧
          (condB C α₁ F₂ = 0 ↔ ∀ s, condDen M α₁ F₂ s = 0))) ∧
    ∀ (O : Finset (X m n)) (T T' : X m n → X m n → PairTable)
      (E E' : ∀ x : X m n, Label (Setting m n) (Outcome m n) x → Ω × Ω → ℝ),
      (∀ x ∈ O, ∀ x' ∈ O, IsSequentialPair x x' → T x x' = T' x x') →
      (∀ x ∈ O, E x = E' x) →
      (clumpCausaloid L T E).ΩC O = (clumpCausaloid L T' E').ΩC O ∧
      (∀ (l : ∀ x : O, omegaOne L x.1) (k : omegaC L O),
        (clumpCausaloid L T E).Λ O l k = (clumpCausaloid L T' E').Λ O l k) ∧
      ∀ α : Lab (Setting m n) (Outcome m n) O,
        (clumpCausaloid L T E).r O α = (clumpCausaloid L T' E').r O α := by
  classical
  let C := actualCausaloid S L
  have hreconstruct := clumping_computes_probabilities ρ hρ M hM S L hL
  have interior := clump_labels_fiducial_interior ρ hρ M hM S L hL
  refine ⟨hreconstruct, fun O h => (interior O h).2, ?_, fun O T T' E E' => clumping_respects_f_locality L T T' E E' O⟩
  intro O₁ O₂ hO α F Y
  let p := C.state M (O₁ ∪ O₂)
  let a := condA C α F Y
  let b := condB C α F
  have hv := regional_outcome_summability S L hO α F
  have hs := scalar_outcome_summable M hO α F Y
  have num s : condNum M α F Y s = a ⬝ᵥ p s := hreconstruct _ _ s
  have den s : condDen M α F s = b ⬝ᵥ p s :=
    (tsum_congr fun y => hreconstruct (O₁ ∪ O₂) (joinLab α (labOf F y)) s).trans (tsum_pairing _ hv _)
  have nneg s : 0 ≤ condNum M α F Y s := M.prob_nonneg _ _
  have nle s : condNum M α F Y s ≤ condDen M α F s :=
    (hs s).le_tsum Y (fun _ _ => M.prob_nonneg _ _)
  have val (c : ℝ) (hc : a = c • b) : IsCondValue M α F Y c := by
    intro s h
    apply (div_eq_iff h).mpr
    rw [num, den, hc, smul_dotProduct, smul_eq_mul]
  have lengthAt (c : ℝ) (hc : a = c • b) (hb : b ≠ 0) :
      IsCondValue M α F Y (euclidLength a / euclidLength b) := by
    intro s h
    have hn : 0 ≤ c := (val c hc s h) ▸ div_nonneg (nneg s) ((nneg s).trans (nle s))
    rw [val c hc s h, hc, length_smul _ _ hn, mul_div_cancel_right₀ _ (length_pos hb).ne']
  refine ⟨hv,hs,fun s => ⟨num s,den s⟩,fun c hc => ⟨val c hc,lengthAt c hc⟩,?_⟩
  intro hO'
  have hp := (interior _ hO').1
  have zero : b = 0 ↔ ∀ s, condDen M α F s = 0 := by
    constructor
    · intro hb s
      simp [den, hb]
    · intro hh
      exact states_separate p hp (fun s => by simpa using (den s).symm.trans (hh s))
  have prop (c : ℝ) (hc : IsCondValue M α F Y c) : a = c • b := by
    apply states_separate p hp
    intro s
    rw [smul_dotProduct, smul_eq_mul, ← num, ← den]
    by_cases h : condDen M α F s = 0
    · rw [h,mul_zero]
      exact le_antisymm ((nle s).trans h.le) (nneg s)
    · exact (div_eq_iff h).mp (hc s h)
  refine ⟨⟨fun ⟨c,hc⟩ => ⟨c,prop c hc⟩,fun ⟨c,hc⟩ => ⟨c,val c hc⟩⟩,prop,?_,zero⟩
  intro hb c hc
  obtain ⟨s,hs⟩ := not_forall.mp (fun h => hb (zero.mpr h))
  exact (hc s hs).symm.trans (lengthAt c (prop c hc) hb s hs)
