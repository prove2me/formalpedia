-- Prove2me | solution 1 for NashPoly.Generic.kkt_points_finite
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:40:15.860216+00:00
-- url     : https://prove2.me/submissions/6aa650ab-ca18-4677-bb72-b0d817c0642b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NashPoly_Generic_Coef
import Definitions.Def_NashPoly_Generic_ComplexKKT
import Theorems.Thm_NashPoly_Generic_theorem_A_1

open MvPolynomial MeasureTheory NashPoly.Generic

namespace SolKKTAux

theorem qmp_comp {I I' : Type} [Fintype I] [Fintype I'] (e : I' → I)
    (he : Function.Injective e) :
    Measure.QuasiMeasurePreserving (fun f : I → ℝ => f ∘ e) volume volume := by
  classical
  let J := {i : I // ¬ i ∈ Set.range e}
  let σ : I' ⊕ J ≃ I :=
    (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun i => i ∈ Set.range e))
  have h1 := (measurePreserving_piCongrLeft (fun _ : I => (volume : Measure ℝ))
    σ).symm.quasiMeasurePreserving
  have h2 := (volume_measurePreserving_sumPiEquivProdPi (fun _ : I' ⊕ J => ℝ)).quasiMeasurePreserving
  have h3 : Measure.QuasiMeasurePreserving
      (Prod.fst : (I' → ℝ) × (J → ℝ) → _) volume volume :=
    Measure.quasiMeasurePreserving_fst
  have := h3.comp (h2.comp h1)
  have key : (fun f : I → ℝ => f ∘ e) = Prod.fst ∘ ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : I' ⊕ J => ℝ) ∘
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : I => ℝ) σ).symm := by
    funext f i'
    simp [σ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply,
      MeasurableEquiv.sumPiEquivProdPi]
    rfl
  rw [key]; exact this

theorem aeval_ofReal {σ : Type} (x : σ → ℝ) (p : MvPolynomial σ ℝ) :
    aeval (fun w => (x w : ℂ)) p = ((eval x p : ℝ) : ℂ) := by
  have := aeval_algebraMap_apply (B := ℂ) x p
  simpa [Function.comp_def] using this

variable {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ) (d : (i : Fin N) → Fin (m i) → ℕ)

noncomputable def mA (A : (i : Fin N) → Finset (Fin (m i))) : Fin N → ℕ := fun i => (A i).card

noncomputable def embA (A : (i : Fin N) → Finset (Fin (m i))) (i : Fin N) (j' : Fin (mA m A i)) : Fin (m i) :=
  ((A i).equivFin.symm j' : Fin (m i))

theorem embA_inj (A : (i : Fin N) → Finset (Fin (m i))) (i : Fin N) :
    Function.Injective (embA m A i) := by
  intro j1 j2 h
  exact (A i).equivFin.symm.injective (Subtype.ext h)

noncomputable def dA (A : (i : Fin N) → Finset (Fin (m i))) : (i : Fin N) → Fin (mA m A i) → ℕ :=
  fun i j' => d i (embA m A i j')

noncomputable def idxE (A : (i : Fin N) → Finset (Fin (m i))) :
    ((Σ i, MonoF n a i) ⊕ (Σ i, Σ j : Fin (mA m A i), MonoG n (mA m A) (dA m d A) i j)) →
      ((Σ i, MonoF n a i) ⊕ (Σ i, Σ j : Fin (m i), MonoG n m d i j))
  | Sum.inl α => Sum.inl α
  | Sum.inr ⟨i, j', β⟩ => Sum.inr ⟨i, embA m A i j', β⟩

theorem idxE_inj (A : (i : Fin N) → Finset (Fin (m i))) : Function.Injective (idxE n m a d A) := by
  rintro (α | ⟨i, j', β⟩) (α' | ⟨i', j'', β'⟩) h
  · simp only [idxE, Sum.inl.injEq] at h; rw [h]
  · simp [idxE] at h
  · simp [idxE] at h
  · simp only [idxE, Sum.inr.injEq] at h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
    have h2 := eq_of_heq h2
    obtain ⟨h3, h4⟩ := Sigma.mk.inj_iff.mp h2
    have := embA_inj m A i h3
    subst this
    have h4 := eq_of_heq h4
    subst h4
    rfl

end SolKKTAux

open SolKKTAux in
theorem solution {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) (hd : ∀ i j, 0 < d i j) :
    ∀ᵐ c ∂(volume : Measure (Coef n m a d)), ∀ E : (i : Fin N) → Finset (Fin (m i)),
      (nepOf c E).KKTSet.Finite := by
  classical
  have hA : ∀ A : (i : Fin N) → Finset (Fin (m i)), ∀ᵐ c ∂(volume : Measure (Coef n m a d)),
      (A1Sol (polyF c) (fun i j' => polyG c i (embA m A i j'))).Finite := by
    intro A
    have h := theorem_A_1 n (mA m A) a (dA m d A) ha (fun i j => hd _ _)
    exact (qmp_comp _ (idxE_inj n m a d A)).ae h
  have hall := ae_all_iff.2 hA
  filter_upwards [hall] with c hc E
  let T : ((i : Fin N) → Finset (Fin (m i))) → Set (Var n → ℝ) := fun A =>
    {x | ∃ μ, ((fun w => (x w : ℂ)), μ) ∈ A1Sol (polyF c) (fun i j' => polyG c i (embA m A i j'))}
  have hT : ∀ A, (T A).Finite := by
    intro A
    have hinj : Set.InjOn (fun x : Var n → ℝ => fun w => (x w : ℂ)) Set.univ := by
      intro x _ y _ h
      funext w
      have := congrFun h w
      simpa using this
    have := ((hc A).image Prod.fst).preimage (hinj.mono (Set.subset_univ _))
    refine this.subset ?_
    rintro x ⟨μ, hμ⟩
    exact ⟨_, hμ, rfl⟩
  refine (Set.finite_iUnion hT).subset ?_
  intro x hx
  obtain ⟨hfeas, lam, hlam⟩ := hx
  let A : (i : Fin N) → Finset (Fin (m i)) := fun i =>
    Finset.univ.filter fun j => eval (blk x i) (polyG c i j) = 0
  refine Set.mem_iUnion.2 ⟨A, fun p => (lam p.1 (embA m A p.1 p.2) : ℂ), fun i => ⟨fun k => ?_,
    fun j' => ?_⟩⟩
  · have hreal : ∑ j', lam i (embA m A i j') * eval (blk x i) (pderiv k (polyG c i (embA m A i j')))
        = eval x (pderiv ⟨i, k⟩ (polyF c i)) := by
      have h1 := (hlam i).1 k
      change ∑ j, lam i j * eval (blk x i) (pderiv k (polyG c i j)) =
        eval x (pderiv ⟨i, k⟩ (polyF c i)) at h1
      rw [← h1]
      have h2 := Equiv.sum_comp (A i).equivFin.symm
        (fun a : A i => lam i a * eval (blk x i) (pderiv k (polyG c i a)))
      simp only [embA]
      erw [h2]
      rw [Finset.sum_coe_sort (A i) (fun j => lam i j * eval (blk x i) (pderiv k (polyG c i j)))]
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
      have hg : eval (blk x i) (polyG c i j) ≠ 0 := by
        intro h; exact hj (by simp [A]; exact h)
      have hjE : j ∉ E i := fun hE => hg ((hfeas i).1 j hE)
      have := ((hlam i).2 j hjE).2
      rw [(mul_eq_zero.mp this).resolve_right hg, zero_mul]
    have e1 := aeval_ofReal x (pderiv ⟨i, k⟩ (polyF c i))
    have e2 : ∀ j', aeval (fun k' => ((x ⟨i, k'⟩ : ℝ) : ℂ)) (pderiv k (polyG c i (embA m A i j'))) =
        ((eval (blk x i) (pderiv k (polyG c i (embA m A i j'))) : ℝ) : ℂ) :=
      fun j' => aeval_ofReal (blk x i) _
    simp only
    rw [e1]
    simp only [e2]
    rw [← hreal]
    push_cast
    rfl
  · have := aeval_ofReal (blk x i) (polyG c i (embA m A i j'))
    simp only
    erw [this]
    have hmem : embA m A i j' ∈ A i := ((A i).equivFin.symm j').2
    simp only [A, Finset.mem_filter] at hmem
    rw [hmem.2]; simp
