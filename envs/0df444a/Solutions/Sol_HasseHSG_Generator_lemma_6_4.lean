-- Prove2me | solution 1 for HasseHSG.Generator.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:58:30.541284+00:00
-- url     : https://prove2.me/submissions/aa1ce4d1-df29-4d4a-aada-68684f80a628

import Mathlib
import Definitions.Def_HasseHSG_Generator_Wronskian
namespace HasseHSG.Generator

/-- Lemma 6.4 (Casoratian, p. 29), for a field `L` with a ring endomorphism `σ`:
`det M_σ(g₁, …, g_m) ≠ 0` iff `g₁, …, g_m` are linearly independent over the fixed field
`L^σ = {u : σ u = u}`. -/
theorem _root_.solution {L : Type*} [Field L] (σ : L →+* L) {m : ℕ} (g : Fin m → L) :
    (casoratiMatrix σ g).det ≠ 0 ↔
      ∀ c : Fin m → L, (∀ j, σ (c j) = c j) → ∑ j, c j * g j = 0 → ∀ j, c j = 0 := by
  classical
  have hentry : ∀ i j, HasseHSG.Generator.casoratiMatrix σ g i j = (⇑σ)^[(i:ℕ)] (g j) := fun i j => rfl
  have hit : ∀ (n : ℕ) (c : Fin m → L), (∀ j, σ (c j) = c j) → ∀ j, (⇑σ)^[n] (c j) = c j := by
    intro n c hc j
    exact Function.iterate_fixed (hc j) n
  constructor
  · intro hdet c hc hsum
    have hMc : (HasseHSG.Generator.casoratiMatrix σ g).mulVec c = 0 := by
      funext i
      have h1 : (⇑σ)^[(i:ℕ)] (∑ j, c j * g j) = 0 := by
        rw [hsum, ← RingHom.coe_pow, map_zero]
      rw [← RingHom.coe_pow, map_sum] at h1
      simp only [map_mul, RingHom.coe_pow, hit _ c hc] at h1
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, hentry]
      rw [← h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hMc
    exact fun j => congrFun this j
  · intro hind hdet
    -- rows of the infinite Casoratian
    set row : ℕ → (Fin m → L) := fun i j => (⇑σ)^[i] (g j) with hrow
    set V : ℕ → Submodule L (Fin m → L) := fun r => Submodule.span L (Set.range fun i : Fin r => row i) with hV
    have hdep : ¬ LinearIndependent L (fun i : Fin m => row i) := by
      intro h
      have hu : IsUnit (HasseHSG.Generator.casoratiMatrix σ g) := by
        rw [← Matrix.linearIndependent_rows_iff_isUnit]
        exact h
      exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero hdet
    have hex : ∃ r, r < m ∧ row r ∈ V r := by
      by_contra hcon
      push Not at hcon
      apply hdep
      have : ∀ r, r ≤ m → LinearIndependent L (fun i : Fin r => row i) := by
        intro r
        induction r with
        | zero => intro _; exact linearIndependent_empty_type
        | succ r ih =>
          intro hr
          rw [linearIndependent_fin_succ']
          exact ⟨ih (by omega), hcon r (by omega)⟩
      exact this m le_rfl
    set r := Nat.find hex with hr
    have hrm : r < m := (Nat.find_spec hex).1
    have hrmem : row r ∈ V r := (Nat.find_spec hex).2
    have hindep : LinearIndependent L (fun i : Fin r => row i) := by
      have : ∀ s, s ≤ r → LinearIndependent L (fun i : Fin s => row i) := by
        intro s
        induction s with
        | zero => intro _; exact linearIndependent_empty_type
        | succ s ih =>
          intro hs
          rw [linearIndependent_fin_succ']
          refine ⟨ih (by omega), fun hmem => ?_⟩
          exact Nat.find_min hex (show s < Nat.find hex by omega) ⟨by omega, hmem⟩
      exact this r le_rfl
    -- the semilinear map applying σ coordinatewise
    set Φ : (Fin m → L) →ₛₗ[σ] (Fin m → L) :=
      { toFun := fun v j => σ (v j)
        map_add' := fun a b => funext fun j => map_add σ _ _
        map_smul' := fun a b => funext fun j => by simp [map_mul] } with hΦ
    have hΦrow : ∀ i, Φ (row i) = row (i+1) := by
      intro i; funext j
      show σ ((⇑σ)^[i] (g j)) = (⇑σ)^[i+1] (g j)
      rw [Function.iterate_succ_apply']
    have hstep : ∀ v ∈ V r, Φ v ∈ V r := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [hΦrow]
        by_cases h : (i:ℕ) + 1 < r
        · exact Submodule.subset_span ⟨⟨i+1, h⟩, rfl⟩
        · have : (i:ℕ) + 1 = r := by have := i.2; omega
          rw [this]; exact hrmem
      | zero => rw [map_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
    have hall : ∀ i, row i ∈ V r := by
      intro i
      induction i with
      | zero =>
        by_cases h : 0 < r
        · exact Submodule.subset_span ⟨⟨0, h⟩, rfl⟩
        · have h0 : r = 0 := by omega
          rw [h0] at hrmem ⊢; exact hrmem
      | succ i ih => rw [← hΦrow]; exact hstep _ ih
    -- the shifted rows span the same space
    have hshift : V r ≤ Submodule.span L (Set.range fun i : Fin r => row (i+1)) := by
      have hind1 : LinearIndependent L (fun i : Fin r => row (i+1)) := by
        rw [Fintype.linearIndependent_iff]
        -- independence is preserved by σ: a nonzero maximal minor stays nonzero
        have hrank : ∃ cols : Fin r → Fin m, (Matrix.of fun (i k : Fin r) => row i (cols k)).det ≠ 0 := by
          set A : Matrix (Fin r) (Fin m) L := Matrix.of fun i j => row i j with hA
          have hrk : A.rank = r := by
            have := LinearIndependent.rank_matrix (M := A) hindep
            simpa using this
          have hcol : Submodule.span L (Set.range A.col) = ⊤ := by
            apply Submodule.eq_top_of_finrank_eq
            rw [← Matrix.rank_eq_finrank_span_cols, hrk, Module.finrank_fin_fun]
          obtain ⟨κ, a, ha_inj, hsp, hli⟩ := exists_linearIndependent' L A.col
          rw [hcol] at hsp
          have hb : Module.Basis κ L (Fin r → L) := Module.Basis.mk hli (by rw [hsp])
          have : Finite κ := hli.finite
          have : Fintype κ := Fintype.ofFinite κ
          have hcard : Fintype.card κ = r := by
            have := Module.finrank_eq_card_basis (Module.Basis.mk hli (show ⊤ ≤ Submodule.span L (Set.range (A.col ∘ a)) by rw [hsp]))
            rw [Module.finrank_fin_fun] at this; exact this.symm
          let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
          refine ⟨a ∘ e, ?_⟩
          have hli2 : LinearIndependent L (fun k : Fin r => A.col (a (e k))) := hli.comp e e.injective
          have hu : IsUnit (Matrix.of fun (i k : Fin r) => row i ((a ∘ e) k)) := by
            rw [← Matrix.linearIndependent_cols_iff_isUnit]
            exact hli2
          exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
        obtain ⟨cols, hdetc⟩ := hrank
        set B : Matrix (Fin r) (Fin r) L := Matrix.of fun (i k : Fin r) => row i (cols k) with hB
        have hdetσ : (σ.mapMatrix B).det ≠ 0 := by
          rw [← RingHom.map_det]
          exact (map_ne_zero σ).2 hdetc
        intro c hc i
        have hv : Matrix.vecMul c (σ.mapMatrix B) = 0 := by
          funext k
          have := congrFun hc (cols k)
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
          rw [Pi.zero_apply, ← this]
          show (∑ i : Fin r, c i * σ (row i (cols k))) = ∑ x : Fin r, c x * row ((x:ℕ)+1) (cols k)
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hΦrow]; rfl
        have := Matrix.eq_zero_of_vecMul_eq_zero hdetσ hv
        exact congrFun this i
      have hle : Submodule.span L (Set.range fun i : Fin r => row (i+1)) ≤ V r :=
        Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hall _)
      have heq : Submodule.span L (Set.range fun i : Fin r => row (i+1)) = V r := by
        apply Submodule.eq_of_le_of_finrank_eq hle
        rw [finrank_span_eq_card hind1, hV, finrank_span_eq_card hindep]
      rw [heq]
    -- the space of relations with every row
    set K : Set (Fin m → L) := {c | ∀ i, ∑ j, c j * row i j = 0} with hK
    have hKchar : ∀ c, (∀ i : Fin r, ∑ j, c j * row i j = 0) → c ∈ K := by
      intro c hc i
      have : ∀ v ∈ V r, ∑ j, c j * v j = 0 := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hc k
        | zero => simp
        | add a b _ _ ha hb => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
        | smul a x _ hx =>
          simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum, hx, mul_zero]
      exact this _ (hall i)
    have hKne : ∃ c ∈ K, c ≠ 0 := by
      set A : (Fin m → L) →ₗ[L] (Fin r → L) := Matrix.mulVecLin (Matrix.of fun (i : Fin r) (j : Fin m) => row i j) with hA
      have : LinearMap.ker A ≠ ⊥ := by
        apply LinearMap.ker_ne_bot_of_finrank_lt
        rw [Module.finrank_fin_fun, Module.finrank_fin_fun]; exact hrm
      obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 this
      refine ⟨c, hKchar c fun i => ?_, hc0⟩
      have := congrFun (LinearMap.mem_ker.1 hc) i
      simp only [hA, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
      rw [← this]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hKσ : ∀ c ∈ K, (fun j => σ (c j)) ∈ K := by
      intro c hc
      have hsh : ∀ i, ∑ j, σ (c j) * row (i+1) j = 0 := by
        intro i
        have := congrArg σ (hc i)
        rw [map_sum, map_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, ← hΦrow]; rfl
      refine hKchar _ fun i => ?_
      have : ∀ v ∈ Submodule.span L (Set.range fun i : Fin r => row (i+1)), ∑ j, σ (c j) * v j = 0 := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hsh _
        | zero => simp
        | add a b _ _ ha hb => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
        | smul a x _ hx =>
          simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum, hx, mul_zero]
      exact this _ (hshift (Submodule.subset_span ⟨i, rfl⟩))
    -- a relation of minimal support is fixed by σ after normalising
    have hmin : ∀ n : ℕ, ∀ c ∈ K, c ≠ 0 → (Finset.univ.filter fun j => c j ≠ 0).card = n → False := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro c hc hc0 hn
        obtain ⟨k, hk⟩ := Function.ne_iff.1 hc0
        simp only [Pi.zero_apply] at hk
        set d : Fin m → L := fun j => (c k)⁻¹ * c j with hd
        have hdK : d ∈ K := by
          intro i
          simp only [hd, mul_assoc, ← Finset.mul_sum, hc i, mul_zero]
        have hdk : d k = 1 := by simp [hd, hk]
        set u : Fin m → L := fun j => σ (d j) - d j with hu
        have huK : u ∈ K := by
          intro i
          simp only [hu, sub_mul, Finset.sum_sub_distrib, hKσ d hdK i, hdK i, sub_zero]
        by_cases hu0 : u = 0
        · have hfix : ∀ j, σ (d j) = d j := fun j => sub_eq_zero.1 (congrFun hu0 j)
          have h0 : ∑ j, d j * g j = 0 := by simpa [hrow] using hdK 0
          have := hind d hfix h0 k
          rw [hdk] at this
          exact one_ne_zero this
        · refine ih _ ?_ u huK hu0 rfl
          rw [← hn]
          refine Finset.card_lt_card ⟨fun j hj => ?_, fun hsub => ?_⟩
          · rw [Finset.mem_filter] at hj ⊢
            refine ⟨hj.1, fun h => hj.2 ?_⟩
            simp [hu, hd, h]
          · have := (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩))).2
            apply this
            simp [hu, hdk]
    obtain ⟨c, hc, hc0⟩ := hKne
    exact hmin _ c hc hc0 rfl


end HasseHSG.Generator

