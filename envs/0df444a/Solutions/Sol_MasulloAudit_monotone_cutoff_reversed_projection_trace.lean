-- Prove2me | solution 1 for MasulloAudit.monotone_cutoff_reversed_projection_trace
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:56:53.360019+00:00
-- url     : https://prove2.me/submissions/c0cd3ed4-045c-42e8-a342-4176b96f60b5

import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Set Filter Topology MasulloGRH
open scoped BigOperators
noncomputable section

private abbrev L := lp (fun _ : ℕ => ℂ) 2
private abbrev H := WithLp 2 (L × L)
private def U := WithLp.prodContinuousLinearEquiv 2 ℂ L L
private def pair (f g : H →L[ℂ] L) : H →L[ℂ] H := U.symm.toContinuousLinearMap.comp (f.prod g)
private def X := WithLp.fstL 2 ℂ L L
private def Y := WithLp.sndL 2 ℂ L L
private def av : H →L[ℂ] L := (1/2:ℂ) • (X+Y)
private def projD := pair av av
private def off := pair av (-av)
private def e (i : ℕ) : L := lp.single 2 i 1
private def ev (i : ℕ) := lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i
private def Q (n : ℕ) : L →L[ℂ] L := ∑ i ∈ Finset.range n, (ev i).smulRight (e i)
private def cut (n : ℕ) := pair ((Q (n+1)).comp X) ((Q n).comp Y)

private theorem cutoff_pair_ext {u v : H} (hx : X u=X v) (hy : Y u=Y v) : u=v :=
  U.injective (Prod.ext hx hy)

@[simp] private theorem X_pair (f g : H →L[ℂ] L) (u : H) : X (pair f g u)=f u := rfl
@[simp] private theorem Y_pair (f g : H →L[ℂ] L) (u : H) : Y (pair f g u)=g u := rfl
@[simp] private theorem X_mk (a b : L) : X (WithLp.toLp 2 (a,b)) = a := rfl
@[simp] private theorem Y_mk (a b : L) : Y (WithLp.toLp 2 (a,b)) = b := rfl
@[simp] private theorem av_apply (u : H) : av u = (1/2:ℂ) • (X u+Y u) := rfl
@[simp] private theorem ev_apply (i : ℕ) (u : L) : ev i u = u i := rfl

private theorem ave_proj (u : H) : av (projD u) = av u := by
  change (1/2:ℂ) • (av u + av u) = av u
  rw [←two_smul ℂ,smul_smul]; norm_num

private theorem proj_sq : projD.comp projD = projD := by
  ext1 u
  apply cutoff_pair_ext <;> exact ave_proj u

private theorem proj_off : projD.comp off=0 := by
  ext1 u
  have h : av (off u) = 0 := by change (1/2:ℂ) • (av u + -av u) = 0; simp
  apply cutoff_pair_ext <;> simpa [projD] using h

private theorem off_proj : off.comp projD = off := by
  ext1 u
  apply cutoff_pair_ext
  · exact ave_proj u
  · exact congrArg Neg.neg (ave_proj u)

private theorem proj_self : IsSelfAdjoint projD := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (av x) (X y) + inner ℂ (av x) (Y y) =
    inner ℂ (X x) (av y) + inner ℂ (Y x) (av y)
  simp
  ring

private theorem Qsum (n : ℕ) (x : L) : Q n x = ∑ i ∈ Finset.range n, lp.single 2 i (x i) := by
  simp only [Q,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,ev_apply]
  exact Finset.sum_congr rfl fun i _ => by simpa [e] using (lp.single_smul (E := fun _ : ℕ => ℂ) 2 i (x i) 1).symm

private theorem Qat (n : ℕ) (x : L) (i : ℕ) : Q n x i = if i<n then x i else 0 := by
  rw [Qsum,lp.coeFn_sum,Finset.sum_apply]
  simp [lp.single_apply,Pi.single_apply]

private theorem Qlimit (x : L) : Tendsto (fun n => Q n x) atTop (𝓝 x) := by
  simpa only [Qsum] using (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ⊤) x).tendsto_sum_nat

private theorem cut_limit (u : H) : Tendsto (fun n => cut n u) atTop (𝓝 u) := by
  have ht := ((Qlimit (X u)).comp (tendsto_add_atTop_nat 1)).prodMk_nhds (Qlimit (Y u))
  exact U.symm.continuous.continuousAt.tendsto.comp ht

-- A finite sum of rank-one operators has the indicated trace, in the campaign's own
-- basis-independent definition. The Riesz representatives convert functionals to vectors.
private theorem rank_trace {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (N : ℕ) (f : ℕ → G →L[ℂ] ℂ) (v : ℕ → G) (A : G →L[ℂ] G)
    (hv : ∀ k, N ≤ k → v k=0) (ha : ∀ u, A u = ∑ k ∈ Finset.range N, (f k u) • v k) :
    IsNuclearOperator A ∧ operatorTrace A = ∑ k ∈ Finset.range N, f k (v k) := by
  let x (k : ℕ) := (InnerProductSpace.toDual ℂ G).symm (f k)
  have hfin (k : ℕ) (hk : k ∉ Finset.range N) : v k=0 := hv k (by simpa using hk)
  have hs : Summable (fun k => ‖x k‖ * ‖v k‖) := (hasSum_sum_of_ne_finset_zero (s := Finset.range N)
    (f := fun k => ‖x k‖ * ‖v k‖) (fun k hk => by simp [hfin k hk])).summable
  have he (u : G) : HasSum (fun k => inner ℂ (x k) u • v k) (A u) := by
    rw [ha]; simpa only [x,InnerProductSpace.toDual_symm_apply] using
      (hasSum_sum_of_ne_finset_zero (s := Finset.range N) (f := fun k => (f k u) • v k) (fun k hk => by simp [hfin k hk]))
  refine ⟨⟨x,v,hs,he⟩,?_⟩
  rw [operatorTrace_of_nuclear_series A x v hs he]
  simpa only [x,InnerProductSpace.toDual_symm_apply] using
    (hasSum_sum_of_ne_finset_zero (s := Finset.range N) (f := fun k => f k (v k)) (fun k hk => by simp [hfin k hk])).tsum_eq

private def phi (j : ℕ) := (ev j).comp av
private def b (n j : ℕ) : H := if j<n then WithLp.toLp 2 (e j,-e j)
  else if j=n then WithLp.toLp 2 (e j,0) else 0

private theorem expansion (n : ℕ) (u : H) :
    cut n (off u) = ∑ k ∈ Finset.range (n+1), phi k u • b n k := by
  apply cutoff_pair_ext
  · change Q (n+1) (av u) = X _
    rw [Qsum,map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have h : j≤n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hx : X (b n j) = e j := by by_cases h' : j<n <;> simp [b,h',show ¬j<n → j=n by omega]
    rw [map_smul,hx]
    change lp.single 2 j (av u j) = av u j • e j
    simpa [e] using lp.single_smul (E := fun _ : ℕ => ℂ) 2 j (av u j) 1
  · change Q n (-av u) = Y _
    rw [Finset.sum_range_succ,map_add,map_smul,show Y (b n n)=0 by simp [b],smul_zero,add_zero,map_sum,Qsum]
    apply Finset.sum_congr rfl
    intro j hj
    have h : j<n := Finset.mem_range.mp hj
    rw [map_smul,show Y (b n j) = -e j by simp [b,h],smul_neg]
    change lp.single 2 j (-(av u j)) = -(av u j • e j)
    rw [lp.single_neg]
    congr 1
    simpa [e] using lp.single_smul (E := fun _ : ℕ => ℂ) 2 j (av u j) 1

private theorem trace_cut (n : ℕ) : IsNuclearOperator ((cut n).comp off) ∧ operatorTrace ((cut n).comp off) = 1/2 := by
  obtain ⟨hn,ht⟩ := rank_trace (n+1) phi (b n) ((cut n).comp off)
    (fun k hk => by simp [b,show ¬k<n by omega,show k≠n by omega]) (expansion n)
  refine ⟨hn,ht.trans ?_⟩
  rw [Finset.sum_range_succ]
  have hz : (∑ k ∈ Finset.range n, phi k (b n k)) = 0 := by
    apply Finset.sum_eq_zero; intro j hj
    have hj' := Finset.mem_range.mp hj
    simp [phi,b,hj']
  rw [hz,zero_add]
  change ev n (av (b n n)) = 1/2
  simp [b,ev_apply,e]

theorem solution :
    let L := lp (fun _ : ℕ => ℂ) 2
    let H := WithLp 2 (L × L)
    ∃ (P A : H →L[ℂ] H) (M : ℕ → H →L[ℂ] H), P.comp P=P ∧ IsSelfAdjoint P ∧
      P.comp A=0 ∧ A.comp P=A ∧
      (∀ n (u : H) j, (M n u).fst j = (if j<n+1 then u.fst j else 0) ∧
        (M n u).snd j = (if j<n then u.snd j else 0)) ∧
      (∀ u, Tendsto (fun n => M n u) atTop (𝓝 u)) ∧
      (∀ n, IsNuclearOperator ((M n).comp (A.comp P)) ∧ operatorTrace ((M n).comp (A.comp P)) = 1/2) := by
  refine ⟨projD,off,cut,proj_sq,proj_self,proj_off,off_proj,?_,cut_limit,?_⟩
  · intro n u j; exact ⟨Qat (n+1) (X u) j,Qat n (Y u) j⟩
  · intro n; rw [off_proj]; exact trace_cut n
