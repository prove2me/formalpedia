-- Prove2me | solution 1 for Monotonicity_Theorem.good_outside_finite_exceptional_set
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T20:30:10.593086+00:00
-- url     : https://prove2.me/submissions/4b881dcd-b5ca-4557-9883-53916d4a36a4

import Theorems.Thm_Monotonicity_Theorem_window_loci_definable
import Theorems.Thm_Monotonicity_Theorem_no_good_window_locus_finite
import Theorems.Thm_Monotonicity_Theorem_definable_interval_dichotomy
import Theorems.Thm_Monotonicity_Theorem_locally_constant_implies_constant
import Theorems.Thm_Monotonicity_Theorem_locally_increasing_implies_increasing
import Theorems.Thm_Monotonicity_Theorem_locally_decreasing_implies_decreasing

set_option autoImplicit false

open Monotonicity_Theorem

private lemma isFinite1_or {R : Type} {F₁ F₂ : Set (Power R 1)}
    (h₁ : IsFinite1 F₁) (h₂ : IsFinite1 F₂) : IsFinite1 (fun x => F₁ x ∨ F₂ x) := by
  obtain ⟨L₁, hL₁⟩ := h₁
  obtain ⟨L₂, hL₂⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_⟩
  intro x
  constructor
  · rintro (h | h)
    · exact List.mem_append.2 (Or.inl ((hL₁ x).1 h))
    · exact List.mem_append.2 (Or.inr ((hL₂ x).1 h))
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact Or.inl ((hL₁ x).2 h)
    · exact Or.inr ((hL₂ x).2 h)

/-- The assembly: good outside a finite exceptional set. -/
theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (hI : IsInfinite1 I) :
    ∃ F : Set (Power R 1), IsFinite1 F ∧
      ∀ u v : R, D.lt u v →
        (∀ x : Power R 1, openInterval D (Endpoint.finite u) (Endpoint.finite v) x → ¬ F x) →
        (let J : Set (Power R 1) := openInterval D (Endpoint.finite u) (Endpoint.finite v)
         ((∀ x (hxI : I x), J x → ∀ y (hyI : I y), J y →
            f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI)) ∨
          (((∀ x (hxI : I x), J x → ∀ y (hyI : I y), J y → Lt1 D x y →
              Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) ∨
            (∀ x (hxI : I x), J x → ∀ y (hyI : I y), J y → Lt1 D x y →
              Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) ∧
           J.Subset (ContinuousPoints D I
             (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun))))) := by
  obtain ⟨hC, hInc, hDec⟩ := window_loci_definable D M f
  obtain ⟨FI, hFIfin, hFI⟩ := definable_interval_dichotomy D ((M.ominimal I).1 f.domain_mem)
  obtain ⟨FC, hFCfin, hFC⟩ := definable_interval_dichotomy D ((M.ominimal _).1 hC)
  obtain ⟨FInc, hFIncfin, hFInc⟩ := definable_interval_dichotomy D ((M.ominimal _).1 hInc)
  obtain ⟨FDec, hFDecfin, hFDec⟩ := definable_interval_dichotomy D ((M.ominimal _).1 hDec)
  have hBad := no_good_window_locus_finite D M f hI
  refine ⟨fun x => FI x ∨ (FC x ∨ (FInc x ∨ (FDec x ∨ setCompl (GoodWindowLocus f) x))), ?_, ?_⟩
  · exact isFinite1_or hFIfin (isFinite1_or hFCfin (isFinite1_or hFIncfin
      (isFinite1_or hFDecfin hBad)))
  · intro u v huv havoid J
    -- the interval is either inside the domain or disjoint from it
    rcases hFI u v huv (fun x hx h => havoid x hx (Or.inl h)) with hsub | hdisj
    · -- pick an interior point and read off its behaviour
      obtain ⟨z, hz₁, hz₂⟩ := D.dense huv
      have hzJ : J (fun _ => z) := ⟨hz₁, hz₂⟩
      have hzgood : GoodWindowLocus f (fun _ => z) := by
        by_contra hcon
        exact havoid (fun _ => z) hzJ (Or.inr (Or.inr (Or.inr (Or.inr hcon))))
      rcases hzgood with hzC | hzInc | hzDec
      · have hJC : J.Subset (ConstWindowLocus f) := by
          rcases hFC u v huv (fun x hx h => havoid x hx (Or.inr (Or.inl h))) with h | h
          · exact h
          · exact absurd hzC (h _ hzJ)
        exact Or.inl (locally_constant_implies_constant D M f u v huv hsub hJC)
      · have hJInc : J.Subset (IncWindowLocus f) := by
          rcases hFInc u v huv (fun x hx h => havoid x hx (Or.inr (Or.inr (Or.inl h)))) with h | h
          · exact h
          · exact absurd hzInc (h _ hzJ)
        exact Or.inr ⟨Or.inl (locally_increasing_implies_increasing D M f u v huv hsub hJInc),
          hsub⟩
      · have hJDec : J.Subset (DecWindowLocus f) := by
          rcases hFDec u v huv
            (fun x hx h => havoid x hx (Or.inr (Or.inr (Or.inr (Or.inl h))))) with h | h
          · exact h
          · exact absurd hzDec (h _ hzJ)
        exact Or.inr ⟨Or.inr (locally_decreasing_implies_decreasing D M f u v huv hsub hJDec),
          hsub⟩
    · -- the interval misses the domain, so the constancy clause is vacuous
      refine Or.inl ?_
      intro x hxI hxJ
      exact absurd hxI (hdisj x hxJ)
