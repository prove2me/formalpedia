-- Prove2me | solution 1 for MasulloAudit.normalized_markushevich_not_schauder
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:49:15.972457+00:00
-- url     : https://prove2.me/submissions/8cc1574c-a3c9-44e8-a09b-58c26a102732

import Mathlib.Analysis.InnerProductSpace.l2Space

open Set Filter Topology
noncomputable section

private abbrev H := lp (fun _ : ℕ => ℝ) 2
private def e (i : ℕ) : H := lp.single 2 i 1
private def v (i : ℕ) : H :=
  if i % 2 = 0 then e i else e (i-1) + (1 / ((i/2:ℕ)+1:ℝ)) • e i
private def f (i : ℕ) : H →L[ℝ] ℝ :=
  let ev := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2
  if i % 2 = 0 then ev i - ((i/2:ℕ)+1:ℝ) • ev (i+1)
  else ((i/2:ℕ)+1:ℝ) • ev i
private def u (i : ℕ) : H := ‖v i‖⁻¹ • v i
private def g (i : ℕ) : H →L[ℝ] ℝ := ‖v i‖ • f i

private theorem paired (i : ℕ) : ∃ k : ℕ, i = 2*k ∨ i = 2*k+1 := ⟨i/2,by omega⟩
@[simp] private theorem coord_e (i j : ℕ) : e i j = if j=i then 1 else 0 := by
  by_cases h : j = i
  · subst j; exact lp.single_apply_self 2 i 1 |>.trans (by simp)
  · rw [if_neg h]; exact lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 i (1:ℝ) h

@[simp] private theorem ve (k : ℕ) : v (2*k) = e (2*k) := by simp [v]
@[simp] private theorem vo (k : ℕ) : v (2*k+1) = e (2*k) + (1/(k+1:ℝ)) • e (2*k+1) := by
  simp [v,show (2*k+1)/2 = k by omega,show (2*k+1)%2 = 1 by omega]
@[simp] private theorem fe (k : ℕ) (x : H) :
    f (2*k) x = x (2*k) - (k+1:ℝ)*x (2*k+1) := by
  simp [f,show (2*k)/2 = k by omega]; rfl
@[simp] private theorem fo (k : ℕ) (x : H) : f (2*k+1) x = (k+1:ℝ)*x (2*k+1) := by
  simp [f,show (2*k+1)/2 = k by omega,show (2*k+1)%2 = 1 by omega]; exact Or.inl rfl

private theorem vec_even (k j : ℕ) : v (2*k) j = e (2*k) j := by rw [ve]
private theorem vec_odd (k j : ℕ) : v (2*k+1) j = e (2*k) j + (1/(k+1:ℝ))*e (2*k+1) j := by rw [vo]; rfl

private theorem biorth (i j : ℕ) : f i (v j) = if i=j then 1 else 0 := by
  obtain ⟨k,rfl|rfl⟩ := paired i <;> obtain ⟨l,rfl|rfl⟩ := paired j
  all_goals
    simp only [fe,fo,vec_odd,vec_even,coord_e]
    by_cases h : k=l
    · subst l
      simp [show 2*k ≠ 2*k+1 by omega,
        show 2*k+1 ≠ 2*k by omega, ne_of_gt (show (0:ℝ)<k+1 by positivity)]
    · simp [show 2*k ≠ 2*l by omega,
        show 2*k+1 ≠ 2*l+1 by omega,show 2*k ≠ 2*l+1 by omega,show 2*k+1 ≠ 2*l by omega,h]

private theorem v_ne (i : ℕ) : v i ≠ 0 := by
  intro h
  simpa [h] using biorth i i

private theorem v_from_u (i : ℕ) : ‖v i‖ • u i = v i := by
  simp [u,smul_smul,norm_ne_zero_iff.mpr (v_ne i)]

private theorem u_unit (i : ℕ) : ‖u i‖ = 1 := by
  simp [u,norm_smul,norm_ne_zero_iff.mpr (v_ne i)]

private theorem u_dense : (Submodule.span ℝ (range u)).topologicalClosure = ⊤ := by
  let K := (Submodule.span ℝ (range u)).topologicalClosure
  have hv (i : ℕ) : v i ∈ K := by
    rw [←v_from_u i]
    exact K.smul_mem _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i,rfl⟩))
  have he (i : ℕ) : e i ∈ K := by
    obtain ⟨k,rfl|rfl⟩ := paired i
    · simpa using hv (2*k)
    · have hm := K.smul_mem (k+1:ℝ) (K.sub_mem (hv (2*k+1)) (hv (2*k)))
      simpa [smul_smul,ne_of_gt (show (0:ℝ)<k+1 by positivity)] using hm
  apply top_unique
  intro x _
  have hm (i : ℕ) : lp.single 2 i (x i) ∈ K := by
    have h := K.smul_mem (x i) (he i)
    simpa [e,←lp.single_smul] using h
  exact ((Submodule.span ℝ (range u)).isClosed_topologicalClosure).mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ⊤) x)
    (.of_forall fun s => K.sum_mem fun i _ => hm i)

private theorem separate (x : H) (hx : ∀ i, g i x = 0) : x = 0 := by
  have hf (i : ℕ) : f i x = 0 := by
    simpa [g,smul_eq_mul,norm_ne_zero_iff.mpr (v_ne i)] using hx i
  ext i
  obtain ⟨k,rfl|rfl⟩ := paired i
  all_goals
    have hodd : x (2*k+1) = 0 := by simpa [ne_of_gt (show (0:ℝ)<k+1 by positivity)] using hf (2*k+1)
    simpa [hodd] using hf (2*k)

private theorem no_basis : ¬∃ b : SchauderBasis ℝ H, ∀ i, b i = u i := by
  rintro ⟨b,hb⟩
  obtain ⟨C,hC⟩ := b.exists_norm_proj_le
  obtain ⟨k,hk⟩ := exists_nat_gt C
  let P := b.proj (2*k+1)
  have proj_v (i : ℕ) : P (v i) = if i < 2*k+1 then v i else 0 := by
    calc P (v i) = ‖v i‖ • P (b i) := by rw [hb,←map_smul,v_from_u]
         _ = _ := by rw [SchauderBasis.proj_apply_basis_mem]; split_ifs <;> simp [hb,v_from_u]
  have hval : P (v (2*k) - v (2*k+1)) = v (2*k) := by
    simp only [map_sub,proj_v,if_pos (show 2*k<2*k+1 by omega),lt_irrefl,if_false,sub_zero]
  have hen (i : ℕ) : ‖e i‖ = 1 := by simp [e,lp.norm_single (by norm_num : (0:ENNReal)<2)]
  have hd : ‖v (2*k)-v (2*k+1)‖ = 1/(k+1:ℝ) := by
    rw [ve,vo,sub_add_cancel_left, norm_neg,norm_smul,hen]
    simp [Real.norm_eq_abs,show (0:ℝ) ≤ k+1 by positivity]
  have h := (P.le_opNorm (v (2*k)-v (2*k+1))).trans
    (mul_le_mul_of_nonneg_right (hC (2*k+1)) (norm_nonneg _))
  rw [hval,hd,ve,hen] at h
  have hh : (k+1:ℝ) ≤ C := by
    rw [mul_one_div] at h
    simpa using (le_div_iff₀ (by positivity : (0:ℝ)<k+1)).mp h
  linarith

theorem solution :
    ∃ (u : ℕ → lp (fun _ : ℕ => ℝ) 2) (g : ℕ → lp (fun _ : ℕ => ℝ) 2 →L[ℝ] ℝ),
      (∀ i, ‖u i‖ = 1) ∧ (∀ i j, g i (u j) = if i=j then 1 else 0) ∧
      (Submodule.span ℝ (range u)).topologicalClosure = ⊤ ∧
      (∀ x, (∀ i, g i x = 0) → x = 0) ∧
      ¬∃ b : SchauderBasis ℝ (lp (fun _ : ℕ => ℝ) 2), ∀ i, b i = u i := by
  refine ⟨u,g,u_unit,?_,u_dense,separate,no_basis⟩
  intro i j
  by_cases h : i=j
  · subst j; simp [g,u,biorth,smul_eq_mul,norm_ne_zero_iff.mpr (v_ne i)]
  · simp [g,u,biorth,h,smul_eq_mul]
