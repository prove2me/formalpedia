-- Prove2me | solution 1 for IntConeFPT.lemma_5_pricer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T14:07:58.199744+00:00
-- url     : https://prove2.me/submissions/57e935c6-00e9-47a3-a841-cb58b4550e68
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation
import Theorems.Thm_IntConeFPT_lemma_29
import Theorems.Thm_IntConeFPT_runsWithin_chain
import Theorems.Thm_IntConeFPT_runsWithin_thread
import Theorems.Thm_IntConeFPT_lemma_5_pricer_perturb_writer
import Theorems.Thm_IntConeFPT_lemma_5_pricer_eval
import Theorems.Thm_IntConeFPT_fiber_vertex_encoding_bound

set_option autoImplicit false

open OnlineCRS.Combine IntConeFPT

namespace IntConeFPT.Lemma5PricerProof

lemma two_atoms (a b P : ℕ) (ha : 2 ≤ a) (hP : 1 ≤ P) (hb : b ≤ P) : a + b ≤ P * a * a := by
  have h1 : a ≤ P * a := Nat.le_mul_of_pos_left a hP
  have h2 : b ≤ P * a := hb.trans (Nat.le_mul_of_pos_right P (by omega))
  have h3 : P * a * 2 ≤ P * a * a := Nat.mul_le_mul_left _ ha
  omega

lemma len_arith (A G R Cv Ce C : ℕ) (hA : 3 ≤ A) (hG : G ≤ A ^ Cv) (hR : R ≤ (A + G) ^ Ce)
    (hC : (Cv + 2) * (Ce + 1) + 1 ≤ C) : G + R + 1 ≤ A ^ C := by
  have hA1 : 1 ≤ A := by omega
  have hpCv : 1 ≤ A ^ Cv := Nat.one_le_pow _ _ (by omega)
  have h1 : A + G ≤ A ^ (Cv + 2) := by
    rw [show A ^ (Cv + 2) = A ^ Cv * A * A by ring]
    exact two_atoms A G _ (by omega) hpCv hG
  have hGM : G ≤ A ^ ((Cv + 2) * (Ce + 1)) :=
    hG.trans (Nat.pow_le_pow_right hA1 (by nlinarith))
  have hRM : R ≤ A ^ ((Cv + 2) * (Ce + 1)) := by
    refine hR.trans ((Nat.pow_le_pow_left h1 Ce).trans ?_)
    rw [← pow_mul]; exact Nat.pow_le_pow_right hA1 (by nlinarith)
  calc G + R + 1 ≤ A ^ ((Cv + 2) * (Ce + 1)) * 3 := by
        have := Nat.one_le_pow ((Cv + 2) * (Ce + 1)) A (by omega); omega
    _ ≤ A ^ ((Cv + 2) * (Ce + 1)) * A := Nat.mul_le_mul_left _ hA
    _ = A ^ ((Cv + 2) * (Ce + 1) + 1) := by ring
    _ ≤ A ^ C := Nat.pow_le_pow_right hA1 hC

lemma time_arith (L A n1 G C1 C29 Ce C : ℕ) (B : ℝ) (hB : 1 ≤ B) (hL : 2 ≤ L)
    (hA : A ≤ L) (hn1 : n1 ≤ (L + 2) ^ C1 + L) (hG : G ≤ n1 ^ C29) (hC1 : C29 ≤ C)
    (hC2 : 2 * (((C1 + 2) * (C29 + 1) + 3) * (Ce + 1)) + 5 ≤ C) :
    ((L : ℝ) + 2) ^ C1 + (B ^ C29 * (n1 : ℝ) ^ C29 + 2 * (A : ℝ) + 3) +
        2 * ((2 * (A : ℝ) + 1 + n1) + 1) +
        ((2 * (A : ℝ) + 1 + (1 + G)) + 2) ^ Ce + 2 * ((2 * (A : ℝ) + 1 + (1 + G)) + 1) ≤
      B ^ C * (L : ℝ) ^ C := by
  obtain ⟨X, hX⟩ : ∃ X, X = L + 2 := ⟨_, rfl⟩
  rw [← hX] at hn1
  have hX4 : 4 ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  have hpC1 : 1 ≤ X ^ C1 := Nat.one_le_pow _ _ (by omega)
  have hn1K : n1 ≤ X ^ (C1 + 2) := by
    rw [show X ^ (C1 + 2) = X ^ C1 * X * X by ring]
    have := two_atoms X (X ^ C1) (X ^ C1) (by omega) hpC1 le_rfl
    omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ ((C1 + 2) * (C29 + 1)) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (Y * X ^ 3) ^ (Ce + 1) := ⟨_, rfl⟩
  have hXY : X ^ (C1 + 2) ≤ Y := hY ▸ Nat.pow_le_pow_right hX1 (by nlinarith)
  have hX_Y : X ≤ Y := by
    have : X ≤ X ^ (C1 + 2) := by
      calc X = X ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right hX1 (by omega)
    omega
  have hC1Y : X ^ C1 ≤ Y := (Nat.pow_le_pow_right hX1 (by omega)).trans hXY
  have hn1C : n1 ^ C29 ≤ Y := by
    refine (Nat.pow_le_pow_left hn1K C29).trans ?_
    rw [← pow_mul, hY]; exact Nat.pow_le_pow_right hX1 (by nlinarith)
  have hGY : G ≤ Y := hG.trans hn1C
  have hAY : A ≤ Y := by omega
  have hX3 : 64 ≤ X ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ X ^ 3 := Nat.pow_le_pow_left hX4 3
  have hYX : Y * 64 ≤ Y * X ^ 3 := Nat.mul_le_mul_left _ hX3
  have hy2 : 2 * A + 1 + (1 + G) + 2 ≤ Y * X ^ 3 := by omega
  have hYX1 : 1 ≤ Y * X ^ 3 := by omega
  have hy2e : (2 * A + 1 + (1 + G) + 2) ^ Ce ≤ Z :=
    hZ ▸ (Nat.pow_le_pow_left hy2 Ce).trans (Nat.pow_le_pow_right hYX1 (by omega))
  have hYZ : Y ≤ Z := by
    have : Y * X ^ 3 ≤ Z := by
      calc Y * X ^ 3 = (Y * X ^ 3) ^ 1 := (pow_one _).symm
        _ ≤ Z := hZ ▸ Nat.pow_le_pow_right hYX1 (by omega)
    omega
  have hZE : Z = X ^ (((C1 + 2) * (C29 + 1) + 3) * (Ce + 1)) := by
    rw [hZ, hY, ← pow_add, ← pow_mul]
  have hXL : X ≤ L ^ 2 := by nlinarith
  have h32 : 32 ≤ L ^ 5 := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ L ^ 5 := Nat.pow_le_pow_left hL 5
  have hZL : 32 * Z ≤ L ^ C := by
    rw [hZE]
    calc 32 * X ^ (((C1 + 2) * (C29 + 1) + 3) * (Ce + 1))
        ≤ L ^ 5 * (L ^ 2) ^ (((C1 + 2) * (C29 + 1) + 3) * (Ce + 1)) :=
          Nat.mul_le_mul h32 (Nat.pow_le_pow_left hXL _)
      _ = L ^ (2 * (((C1 + 2) * (C29 + 1) + 3) * (Ce + 1)) + 5) := by ring
      _ ≤ L ^ C := Nat.pow_le_pow_right (by omega) hC2
  have hBp : 1 ≤ B ^ C29 := one_le_pow₀ hB
  have hBC : B ^ C29 ≤ B ^ C := pow_le_pow_right₀ hB hC1
  have rX : ((L : ℝ) + 2) ^ C1 = ((X ^ C1 : ℕ) : ℝ) := by rw [hX]; push_cast; ring
  have rn : (n1 : ℝ) ^ C29 = ((n1 ^ C29 : ℕ) : ℝ) := by push_cast; ring
  have ry : ((2 * (A : ℝ) + 1 + (1 + G)) + 2) ^ Ce =
      (((2 * A + 1 + (1 + G) + 2) ^ Ce : ℕ) : ℝ) := by push_cast; ring
  have rL : (L : ℝ) ^ C = ((L ^ C : ℕ) : ℝ) := by push_cast; ring
  rw [rX, rn, ry, rL]
  have e1 : ((X ^ C1 : ℕ) : ℝ) ≤ Y := by exact_mod_cast hC1Y
  have e2 : ((n1 ^ C29 : ℕ) : ℝ) ≤ Y := by exact_mod_cast hn1C
  have e3 : (A : ℝ) ≤ Y := by exact_mod_cast hAY
  have e4 : (n1 : ℝ) ≤ Y := by exact_mod_cast (hn1K.trans hXY)
  have e5 : (G : ℝ) ≤ Y := by exact_mod_cast hGY
  have e6 : (((2 * A + 1 + (1 + G) + 2) ^ Ce : ℕ) : ℝ) ≤ Z := by exact_mod_cast hy2e
  have e7 : (Y : ℝ) ≤ Z := by exact_mod_cast hYZ
  have e8 : (32 : ℝ) * Z ≤ ((L ^ C : ℕ) : ℝ) := by exact_mod_cast hZL
  have key : B ^ C29 * ((n1 ^ C29 : ℕ) : ℝ) ≤ B ^ C29 * Z :=
    mul_le_mul_of_nonneg_left (e2.trans e7) (by linarith)
  have hZ0 : (0 : ℝ) ≤ Z := Nat.cast_nonneg _
  have e9 : (4 : ℝ) ≤ Y := by exact_mod_cast (hX4.trans hX_Y)
  have hstep : B ^ C29 * Z + 31 * Z ≤ B ^ C29 * (32 * Z) := by nlinarith
  calc _ ≤ B ^ C29 * Z + 31 * Z := by linarith
    _ ≤ B ^ C29 * (32 * Z) := hstep
    _ ≤ B ^ C * ((L ^ C : ℕ) : ℝ) := mul_le_mul hBC e8 (by positivity) (by linarith)

lemma runsWithin_mono {M : Machine} {x y : List Sym} {T U : ℝ} (h : RunsWithin M x y T)
    (hTU : T ≤ U) : RunsWithin M x y U := by
  obtain ⟨m, hm, hr⟩ := h
  exact ⟨m, hm.trans hTU, hr⟩

lemma oracleBound_eq_pow (C d L : ℕ) :
    oracleBound C d L =
      ((2 : ℝ) ^ ((d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1))) ^ C * (L : ℝ) ^ C := by
  unfold oracleBound
  congr 1
  rw [← Real.rpow_natCast _ C, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

lemma one_le_base (d : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) := by
  apply Real.one_le_rpow (by norm_num)
  apply mul_nonneg (by positivity)
  apply Real.logb_nonneg (by norm_num)
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  linarith

/-- The secondary objective `p(x) = Σ_i ((x_i − r_i)/2^d)²` is convex on all of `ℝ^d`. -/
lemma p_convex (d : ℕ) (c : Fin d → ℝ) :
    ConvexOn ℝ Set.univ (fun x : Fin d → ℝ => ∑ i, ((x i - c i) / 2 ^ d) ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hD : (0 : ℝ) < 2 ^ d := by positivity
  set u := (x i - c i) / 2 ^ d
  set v := (y i - c i) / 2 ^ d
  have hxy : (a * x i + b * y i - c i) / 2 ^ d = a * u + b * v := by
    simp only [u, v]; field_simp; linear_combination (c i) * hab
  rw [hxy]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg (u - v), mul_nonneg ha hb]

lemma encLocal_length_ge (I : Instance) (t : Fin I.τ) (r : Residue I.d) :
    3 ≤ (encLocal I t r).length := by
  simp [encLocal, encInstance]
  omega

lemma encInstance_le_encLocal (I : Instance) (t : Fin I.τ) (r : Residue I.d) :
    (encInstance I).length ≤ (encLocal I t r).length := by
  simp [encLocal]

lemma frame_length (c y : List Sym) :
    (c.flatMap (fun s => [(0 : Sym), s]) ++ 1 :: y).length = 2 * c.length + 1 + y.length := by
  simp [List.length_flatMap]; ring

end IntConeFPT.Lemma5PricerProof

open IntConeFPT.Lemma5PricerProof

theorem solution :
    ∃ C : ℕ, ∃ P : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d), (I.Sr t r).Nonempty →
      ∀ (ε : ℚ), 0 ≤ ε → ∀ (ax : Fin I.d → ℚ) (au : Fin I.k → ℚ),
        let p : (Fin I.d → ℝ) → ℝ := fun x => ∑ i, ((x i - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2
        let q := encLocal I t r ++ encRat ε ++ [3] ++ encVec ax ++ encVec au
        ∃ (x : Fin I.d → ℤ) (u : Fin I.k → ℚ) (cq sq : ℚ),
          ratGen x u ∈ I.Vr t r ∧ (cq : ℝ) = I.f t (fun i => (x i : ℝ)) ∧
          (sq : ℝ) = p (fun i => (x i : ℝ)) ∧
          (∀ g ∈ I.Sr t r, (cq : ℝ) + (ε : ℝ) * sq - pairing (ratPair ax au) (ratGen x u).toReal ≤
            I.f t (fun i => (g.1 i : ℝ)) + (ε : ℝ) * p (fun i => (g.1 i : ℝ)) -
              pairing (ratPair ax au) g.toReal) ∧
          (encGen x u ++ encRat cq ++ encRat sq ++ [3]).length ≤ (encLocal I t r).length ^ C ∧
          RunsWithin P q (encGen x u ++ encRat cq ++ encRat sq ++ [3])
            (oracleBound C I.d q.length) := by
  obtain ⟨C29, M29, h29⟩ := IntConeFPT.lemma_29
  obtain ⟨C1, W1, hW1⟩ := IntConeFPT.lemma_5_pricer_perturb_writer
  obtain ⟨Ce, E, hE⟩ := IntConeFPT.lemma_5_pricer_eval
  obtain ⟨Cv, hV⟩ := IntConeFPT.fiber_vertex_encoding_bound
  obtain ⟨M29t, hT⟩ := IntConeFPT.runsWithin_thread M29
  obtain ⟨W12, h12⟩ := IntConeFPT.runsWithin_chain W1 M29t
  obtain ⟨W123, h123⟩ := IntConeFPT.runsWithin_chain W12 E
  refine ⟨C29 + (2 * (((C1 + 2) * (C29 + 1) + 3) * (Ce + 1)) + 5) +
      ((Cv + 2) * (Ce + 1) + 1), W123, ?_⟩
  intro I hI t r hne ε hε ax au p q
  obtain ⟨D, c, hf, hlen1, hrun1⟩ := hW1 I hI t r ε hε ax au
  -- the perturbed instance `I'`, with cost `f + ε p`
  let I' : Instance := { I with deg := D, coeff := c }
  have hf' : ∀ (t' : Fin I.τ) (y : Fin I.d → ℝ), I'.f t' y = I.f t' y + (ε : ℝ) * p y := hf
  have hV' : I'.Valid := by
    refine ⟨hI.one_le_d, hI.one_le_τ, hI.bounded, fun t' => ?_⟩
    have hfun : I'.f t' = fun y => I.f t' y + (ε : ℝ) • p y := by
      funext y; rw [hf', smul_eq_mul]
    rw [hfun]
    have hpc : ConvexOn ℝ (I.Px t') p :=
      (p_convex I.d (fun i => ((r i : ℕ) : ℝ))).subset (Set.subset_univ _) (hI.convex t').1
    exact (hI.convex t').add (hpc.smul (by exact_mod_cast hε))
  obtain ⟨o, ho_none, ho_some, hrun2⟩ := h29 I' hV' t r ax au
  have hSr' : I'.Sr t r = I.Sr t r := rfl
  obtain ⟨⟨x, u⟩, rfl⟩ : ∃ g, o = some g := by
    cases o with
    | none => exact absurd (ho_none.mp rfl) (by rw [hSr']; exact hne.ne_empty)
    | some g => exact ⟨g, rfl⟩
  obtain ⟨hVr, hmin, hgen⟩ := ho_some (x, u) rfl
  have hVr' : ratGen x u ∈ I.Vr t r := hVr
  obtain ⟨cq, sq, hcq, hsq, hlen3, hrun3⟩ := hE I hI t r x u
  refine ⟨x, u, cq, sq, hVr', hcq, hsq, ?_, ?_, ?_⟩
  · -- optimality transfers from `f + ε p` (the cost of `I'`)
    intro g hg
    have h := hmin g hg
    simp only [hf'] at h
    rw [hcq, hsq]
    linarith
  · -- output length
    have hG := hV I hI t r x u hVr'
    have hGA : (encGen x u).length ≤ (encLocal I t r).length ^ Cv :=
      hG.trans (Nat.pow_le_pow_left (encInstance_le_encLocal I t r) _)
    have hlen : (encGen x u ++ encRat cq ++ encRat sq ++ [3]).length =
        (encGen x u).length + (encRat cq ++ encRat sq).length + 1 := by
      simp; ring
    rw [hlen]
    have hA3 := encLocal_length_ge I t r
    refine (len_arith _ _ _ Cv Ce _ hA3 hGA hlen3 le_rfl).trans ?_
    exact Nat.pow_le_pow_right (by omega) (by omega)
  · -- running time: writer, then threaded Lemma 29, then evaluator
    set A := (encLocal I t r).length with hA
    set inp29 := encLocal I' t r ++ encVec ax ++ encVec au with hinp29
    set G := (encGen x u).length with hGdef
    have hrun2t := hT (encLocal I t r) inp29 (encPricing (some (x, u))) _ hrun2
    have hrun12 := h12 q _ _ _ _ hrun1 hrun2t
    have hrun123 := h123 q _ _ _ _ hrun12 hrun3
    refine runsWithin_mono hrun123 ?_
    rw [frame_length, frame_length, oracleBound_eq_pow, oracleBound_eq_pow]
    have hpl : (encPricing (some (x, u))).length = 1 + G := by
      simp [encPricing, G]; omega
    rw [hpl]
    have hAq : A ≤ q.length := by simp [q, A]
    have hA3 : 3 ≤ A := encLocal_length_ge I t r
    have hn1 : inp29.length ≤ (q.length + 2) ^ C1 + q.length := by
      have hl1 : (encLocal I' t r).length ≤ (q.length + 2) ^ C1 := hlen1
      have : (encVec ax ++ encVec au).length ≤ q.length := by
        simp only [q, List.length_append]; omega
      simp only [inp29, List.length_append] at this ⊢
      omega
    have hG29 : G ≤ inp29.length ^ C29 :=
      hgen.trans (Nat.pow_le_pow_left (by simp [inp29, encLocal]) _)
    have key := time_arith q.length A inp29.length G C1 C29 Ce
      (C29 + (2 * (((C1 + 2) * (C29 + 1) + 3) * (Ce + 1)) + 5) + ((Cv + 2) * (Ce + 1) + 1))
      _ (one_le_base I.d) (by omega) hAq hn1 hG29 (by omega) (by omega)
    push_cast at key ⊢
    linarith
