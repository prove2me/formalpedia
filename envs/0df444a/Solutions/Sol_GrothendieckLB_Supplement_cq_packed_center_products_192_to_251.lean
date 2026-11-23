-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_packed_center_products_192_to_251
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:30:58.938946+00:00
-- url     : https://prove2.me/submissions/e197e797-0309-4f17-8c4b-a93c91b58c93

import Definitions.Def_GrothendieckLB_Supplement_cqHeadSumProducts
open GrothendieckLB.Supplement CQHeadArithmetic CQHeadCertificate CQHeadSum
set_option maxHeartbeats 120000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace FastEvidence
private def wpar (a : ℕ) := (a+1)%2
private def rawB (u : Packed) (k : ℕ) : Interval := ⟨getN u 2 16 k 0,getN u 2 16 k 1⟩
private def X (a : ℕ) (u : Packed) (k : ℕ) :=
  if a+2*k+wpar a ≤ 251 then rawB u k else zeroInterval
private def Y (a : ℕ) (v : Packed) (k : ℕ) :=
  if a ≤ 2*k+a%2 then rawB v k else zeroInterval
private def G (a : ℕ) (u v : Packed) (k : ℕ) : Bool :=
  let x := X a u k
  let y := Y a v k
  decide (|center x| ≤ 2^148 ∧ 0 ≤ width x ∧ width x ≤ 1 ∧
    |center y| ≤ 2^146 ∧ 0 ≤ width y ∧ width y ≤ 256)
private def A (a : ℕ) (u : Packed) (k : ℕ) : ℤ := ((if wpar a=0 then 1 else -1):ℤ)*center (X a u k)
private def V (a : ℕ) (v : Packed) (k : ℕ) : ℤ := center (Y a v k)
private def U (a : ℕ) := entry default weightsData a
private def T (a : ℕ) := entry default powersData a
private theorem wp (a j : ℕ) (h : j%2=wpar a) : w a j=X a (U a) (j/2) := by
  unfold wpar at h
  have e : a+2*(j/2)+(a+1)%2=a+j := by omega
  simp only [w,weight,getB,h,if_true,X,U,rawB,wpar,e]
private theorem pp (a j : ℕ) (h : j%2=a%2) : p a j=Y a (T a) (j/2) := by
  have e : 2*(j/2)+a%2=j := by omega
  simp only [p,power,getB,h,if_true,Y,T,rawB,e]
private theorem wn (a j : ℕ) (h : j%2 ≠ wpar a) : w a j=zeroInterval := by
  unfold w weight getB
  simp [wpar] at h
  split <;> simp_all
private theorem pn (a j : ℕ) (h : j%2 ≠ a%2) : p a j=zeroInterval := by
  simp [p,power,getB,h]
private theorem wpSign (a j : ℕ) (h : j%2=wpar a) :
    (-1:ℤ)^j=(if wpar a=0 then 1 else -1) := by
  rw [←h]
  have h0 : j=2*(j/2)+j%2 := by omega
  conv_lhs => rw [h0,pow_add,pow_mul]
  by_cases h1 : j%2=0
  · simp [h1]
  · have h2 : j%2=1 := by omega
    simp [h2]
private theorem eW (a j : ℕ) :
    wc a j=if j%2=wpar a then A a (U a) (j/2) else 0 := by
  split
  · rename_i h; rw [wc,wp _ _ h,wpSign _ _ h];rfl
  · rename_i h; simp [wc,wn _ _ h,center,zeroInterval]
private theorem eP (a j : ℕ) :
    pc a j=if j%2=a%2 then V a (T a) (j/2) else 0 := by
  split
  · rename_i h; rw [pc,pp _ _ h];rfl
  · rename_i h; simp [pc,pn _ _ h,center,zeroInterval]

private def fast (f : ℕ → ℤ) (n i : ℕ) : ℤ :=
  match n with | 0 => 0 | k+1 => f i+(base*base)*fast f k (i+1)
private theorem pairEval {f g : ℕ → ℤ} {par : ℕ} (hp : par < 2)
    (h : ∀ j, f j=if j%2=par then g (j/2) else 0) (n i : ℕ) :
    pack base (fun j => f (2*i+j)) (2*n)=base^par*fast g n i := by
  induction n generalizing i with
  | zero => simp [pack,fast]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,pack,pack,fast]
    have ee : (fun j => f (2*i+(j+1+1))) = fun j => f (2*(i+1)+j) := by funext j;congr 1;omega
    rw [ee,ih,h (2*i+0),h (2*i+(0+1))]
    have p0 : (2*i+0)%2=0 := by omega
    have p1 : (2*i+(0+1))%2=1 := by omega
    have d0 : (2*i+0)/2=i := by omega
    have d1 : (2*i+(0+1))/2=i := by omega
    rcases (show par=0 ∨ par=1 by omega) with rfl|rfl <;> simp [p0,p1,d0,d1,mul_assoc]

private theorem fastRow (a : ℕ) {u v : Packed} (hu : U a=u) (hv : T a=v)
    (hprod : row a=(base^(wpar a)*fast (A a u) 126 0)*(base^(a%2)*fast (V a v) 126 0))
    (hg : (List.range 126).all (G a u v)=true) : rowHolds a := by
  subst u v
  refine ⟨?_,?_⟩
  · have he := pairEval (Nat.mod_lt (a+1) (by decide) : wpar a < 2) (eW a) 126 0
    have hf := pairEval (Nat.mod_lt a (by decide)) (eP a) 126 0
    have he' : pack base (wc a) 252=base^(wpar a)*fast (A a (U a)) 126 0 := by
      simpa only [Nat.mul_zero,Nat.zero_add,show 2*126=252 by decide] using! he
    have hf' : pack base (pc a) 252=base^(a%2)*fast (V a (T a)) 126 0 := by
      simpa only [Nat.mul_zero,Nat.zero_add,show 2*126=252 by decide] using! hf
    rw [rowProduct,he',hf']
    exact hprod
  · apply List.all_eq_true.mpr
    intro j hj
    have hn := List.mem_range.mp hj
    have hex := of_decide_eq_true (List.all_eq_true.mp hg (j/2) (List.mem_range.mpr (by omega)))
    unfold good
    apply decide_eq_true
    by_cases h0 : j%2=wpar a
    · have h1 : j%2 ≠ a%2 := by unfold wpar at h0;omega
      rw [wp _ _ h0,pn _ _ h1]
      exact ⟨hex.1,hex.2.1,hex.2.2.1,by decide +kernel⟩
    · have h1 : j%2=a%2 := by unfold wpar at h0; omega
      rw [wn _ _ h0,pp _ _ h1]
      exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,hex.2.2.2⟩
private def W192 : Packed := eval% U 192
private def P192 : Packed := eval% T 192
private theorem ok192 : rowHolds 192 := fastRow 192 (u:=W192) (v:=P192) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W193 : Packed := eval% U 193
private def P193 : Packed := eval% T 193
private theorem ok193 : rowHolds 193 := fastRow 193 (u:=W193) (v:=P193) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W194 : Packed := eval% U 194
private def P194 : Packed := eval% T 194
private theorem ok194 : rowHolds 194 := fastRow 194 (u:=W194) (v:=P194) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W195 : Packed := eval% U 195
private def P195 : Packed := eval% T 195
private theorem ok195 : rowHolds 195 := fastRow 195 (u:=W195) (v:=P195) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W196 : Packed := eval% U 196
private def P196 : Packed := eval% T 196
private theorem ok196 : rowHolds 196 := fastRow 196 (u:=W196) (v:=P196) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W197 : Packed := eval% U 197
private def P197 : Packed := eval% T 197
private theorem ok197 : rowHolds 197 := fastRow 197 (u:=W197) (v:=P197) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W198 : Packed := eval% U 198
private def P198 : Packed := eval% T 198
private theorem ok198 : rowHolds 198 := fastRow 198 (u:=W198) (v:=P198) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W199 : Packed := eval% U 199
private def P199 : Packed := eval% T 199
private theorem ok199 : rowHolds 199 := fastRow 199 (u:=W199) (v:=P199) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W200 : Packed := eval% U 200
private def P200 : Packed := eval% T 200
private theorem ok200 : rowHolds 200 := fastRow 200 (u:=W200) (v:=P200) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W201 : Packed := eval% U 201
private def P201 : Packed := eval% T 201
private theorem ok201 : rowHolds 201 := fastRow 201 (u:=W201) (v:=P201) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W202 : Packed := eval% U 202
private def P202 : Packed := eval% T 202
private theorem ok202 : rowHolds 202 := fastRow 202 (u:=W202) (v:=P202) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W203 : Packed := eval% U 203
private def P203 : Packed := eval% T 203
private theorem ok203 : rowHolds 203 := fastRow 203 (u:=W203) (v:=P203) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W204 : Packed := eval% U 204
private def P204 : Packed := eval% T 204
private theorem ok204 : rowHolds 204 := fastRow 204 (u:=W204) (v:=P204) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W205 : Packed := eval% U 205
private def P205 : Packed := eval% T 205
private theorem ok205 : rowHolds 205 := fastRow 205 (u:=W205) (v:=P205) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W206 : Packed := eval% U 206
private def P206 : Packed := eval% T 206
private theorem ok206 : rowHolds 206 := fastRow 206 (u:=W206) (v:=P206) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W207 : Packed := eval% U 207
private def P207 : Packed := eval% T 207
private theorem ok207 : rowHolds 207 := fastRow 207 (u:=W207) (v:=P207) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W208 : Packed := eval% U 208
private def P208 : Packed := eval% T 208
private theorem ok208 : rowHolds 208 := fastRow 208 (u:=W208) (v:=P208) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W209 : Packed := eval% U 209
private def P209 : Packed := eval% T 209
private theorem ok209 : rowHolds 209 := fastRow 209 (u:=W209) (v:=P209) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W210 : Packed := eval% U 210
private def P210 : Packed := eval% T 210
private theorem ok210 : rowHolds 210 := fastRow 210 (u:=W210) (v:=P210) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W211 : Packed := eval% U 211
private def P211 : Packed := eval% T 211
private theorem ok211 : rowHolds 211 := fastRow 211 (u:=W211) (v:=P211) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W212 : Packed := eval% U 212
private def P212 : Packed := eval% T 212
private theorem ok212 : rowHolds 212 := fastRow 212 (u:=W212) (v:=P212) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W213 : Packed := eval% U 213
private def P213 : Packed := eval% T 213
private theorem ok213 : rowHolds 213 := fastRow 213 (u:=W213) (v:=P213) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W214 : Packed := eval% U 214
private def P214 : Packed := eval% T 214
private theorem ok214 : rowHolds 214 := fastRow 214 (u:=W214) (v:=P214) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W215 : Packed := eval% U 215
private def P215 : Packed := eval% T 215
private theorem ok215 : rowHolds 215 := fastRow 215 (u:=W215) (v:=P215) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W216 : Packed := eval% U 216
private def P216 : Packed := eval% T 216
private theorem ok216 : rowHolds 216 := fastRow 216 (u:=W216) (v:=P216) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W217 : Packed := eval% U 217
private def P217 : Packed := eval% T 217
private theorem ok217 : rowHolds 217 := fastRow 217 (u:=W217) (v:=P217) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W218 : Packed := eval% U 218
private def P218 : Packed := eval% T 218
private theorem ok218 : rowHolds 218 := fastRow 218 (u:=W218) (v:=P218) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W219 : Packed := eval% U 219
private def P219 : Packed := eval% T 219
private theorem ok219 : rowHolds 219 := fastRow 219 (u:=W219) (v:=P219) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W220 : Packed := eval% U 220
private def P220 : Packed := eval% T 220
private theorem ok220 : rowHolds 220 := fastRow 220 (u:=W220) (v:=P220) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W221 : Packed := eval% U 221
private def P221 : Packed := eval% T 221
private theorem ok221 : rowHolds 221 := fastRow 221 (u:=W221) (v:=P221) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W222 : Packed := eval% U 222
private def P222 : Packed := eval% T 222
private theorem ok222 : rowHolds 222 := fastRow 222 (u:=W222) (v:=P222) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W223 : Packed := eval% U 223
private def P223 : Packed := eval% T 223
private theorem ok223 : rowHolds 223 := fastRow 223 (u:=W223) (v:=P223) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W224 : Packed := eval% U 224
private def P224 : Packed := eval% T 224
private theorem ok224 : rowHolds 224 := fastRow 224 (u:=W224) (v:=P224) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W225 : Packed := eval% U 225
private def P225 : Packed := eval% T 225
private theorem ok225 : rowHolds 225 := fastRow 225 (u:=W225) (v:=P225) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W226 : Packed := eval% U 226
private def P226 : Packed := eval% T 226
private theorem ok226 : rowHolds 226 := fastRow 226 (u:=W226) (v:=P226) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W227 : Packed := eval% U 227
private def P227 : Packed := eval% T 227
private theorem ok227 : rowHolds 227 := fastRow 227 (u:=W227) (v:=P227) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W228 : Packed := eval% U 228
private def P228 : Packed := eval% T 228
private theorem ok228 : rowHolds 228 := fastRow 228 (u:=W228) (v:=P228) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W229 : Packed := eval% U 229
private def P229 : Packed := eval% T 229
private theorem ok229 : rowHolds 229 := fastRow 229 (u:=W229) (v:=P229) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W230 : Packed := eval% U 230
private def P230 : Packed := eval% T 230
private theorem ok230 : rowHolds 230 := fastRow 230 (u:=W230) (v:=P230) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W231 : Packed := eval% U 231
private def P231 : Packed := eval% T 231
private theorem ok231 : rowHolds 231 := fastRow 231 (u:=W231) (v:=P231) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W232 : Packed := eval% U 232
private def P232 : Packed := eval% T 232
private theorem ok232 : rowHolds 232 := fastRow 232 (u:=W232) (v:=P232) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W233 : Packed := eval% U 233
private def P233 : Packed := eval% T 233
private theorem ok233 : rowHolds 233 := fastRow 233 (u:=W233) (v:=P233) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W234 : Packed := eval% U 234
private def P234 : Packed := eval% T 234
private theorem ok234 : rowHolds 234 := fastRow 234 (u:=W234) (v:=P234) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W235 : Packed := eval% U 235
private def P235 : Packed := eval% T 235
private theorem ok235 : rowHolds 235 := fastRow 235 (u:=W235) (v:=P235) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W236 : Packed := eval% U 236
private def P236 : Packed := eval% T 236
private theorem ok236 : rowHolds 236 := fastRow 236 (u:=W236) (v:=P236) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W237 : Packed := eval% U 237
private def P237 : Packed := eval% T 237
private theorem ok237 : rowHolds 237 := fastRow 237 (u:=W237) (v:=P237) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W238 : Packed := eval% U 238
private def P238 : Packed := eval% T 238
private theorem ok238 : rowHolds 238 := fastRow 238 (u:=W238) (v:=P238) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W239 : Packed := eval% U 239
private def P239 : Packed := eval% T 239
private theorem ok239 : rowHolds 239 := fastRow 239 (u:=W239) (v:=P239) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W240 : Packed := eval% U 240
private def P240 : Packed := eval% T 240
private theorem ok240 : rowHolds 240 := fastRow 240 (u:=W240) (v:=P240) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W241 : Packed := eval% U 241
private def P241 : Packed := eval% T 241
private theorem ok241 : rowHolds 241 := fastRow 241 (u:=W241) (v:=P241) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W242 : Packed := eval% U 242
private def P242 : Packed := eval% T 242
private theorem ok242 : rowHolds 242 := fastRow 242 (u:=W242) (v:=P242) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W243 : Packed := eval% U 243
private def P243 : Packed := eval% T 243
private theorem ok243 : rowHolds 243 := fastRow 243 (u:=W243) (v:=P243) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W244 : Packed := eval% U 244
private def P244 : Packed := eval% T 244
private theorem ok244 : rowHolds 244 := fastRow 244 (u:=W244) (v:=P244) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W245 : Packed := eval% U 245
private def P245 : Packed := eval% T 245
private theorem ok245 : rowHolds 245 := fastRow 245 (u:=W245) (v:=P245) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W246 : Packed := eval% U 246
private def P246 : Packed := eval% T 246
private theorem ok246 : rowHolds 246 := fastRow 246 (u:=W246) (v:=P246) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W247 : Packed := eval% U 247
private def P247 : Packed := eval% T 247
private theorem ok247 : rowHolds 247 := fastRow 247 (u:=W247) (v:=P247) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W248 : Packed := eval% U 248
private def P248 : Packed := eval% T 248
private theorem ok248 : rowHolds 248 := fastRow 248 (u:=W248) (v:=P248) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W249 : Packed := eval% U 249
private def P249 : Packed := eval% T 249
private theorem ok249 : rowHolds 249 := fastRow 249 (u:=W249) (v:=P249) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W250 : Packed := eval% U 250
private def P250 : Packed := eval% T 250
private theorem ok250 : rowHolds 250 := fastRow 250 (u:=W250) (v:=P250) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W251 : Packed := eval% U 251
private def P251 : Packed := eval% T 251
private theorem ok251 : rowHolds 251 := fastRow 251 (u:=W251) (v:=P251) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
end FastEvidence
open FastEvidence in
theorem solution : ∀ a : ℕ, 192 ≤ a → a < 252 → rowHolds a := by
  intro a hl hu
  by_cases h222 : a < 222
  ·
    by_cases h207 : a < 207
    ·
      by_cases h199 : a < 199
      ·
        by_cases h195 : a < 195
        ·
          rcases (show a=192 ∨ a=193 ∨ a=194 by omega) with rfl|rfl|rfl
          · exact ok192
          · exact ok193
          · exact ok194
        ·
          rcases (show a=195 ∨ a=196 ∨ a=197 ∨ a=198 by omega) with rfl|rfl|rfl|rfl
          · exact ok195
          · exact ok196
          · exact ok197
          · exact ok198
      ·
        by_cases h203 : a < 203
        ·
          rcases (show a=199 ∨ a=200 ∨ a=201 ∨ a=202 by omega) with rfl|rfl|rfl|rfl
          · exact ok199
          · exact ok200
          · exact ok201
          · exact ok202
        ·
          rcases (show a=203 ∨ a=204 ∨ a=205 ∨ a=206 by omega) with rfl|rfl|rfl|rfl
          · exact ok203
          · exact ok204
          · exact ok205
          · exact ok206
    ·
      by_cases h214 : a < 214
      ·
        by_cases h210 : a < 210
        ·
          rcases (show a=207 ∨ a=208 ∨ a=209 by omega) with rfl|rfl|rfl
          · exact ok207
          · exact ok208
          · exact ok209
        ·
          rcases (show a=210 ∨ a=211 ∨ a=212 ∨ a=213 by omega) with rfl|rfl|rfl|rfl
          · exact ok210
          · exact ok211
          · exact ok212
          · exact ok213
      ·
        by_cases h218 : a < 218
        ·
          rcases (show a=214 ∨ a=215 ∨ a=216 ∨ a=217 by omega) with rfl|rfl|rfl|rfl
          · exact ok214
          · exact ok215
          · exact ok216
          · exact ok217
        ·
          rcases (show a=218 ∨ a=219 ∨ a=220 ∨ a=221 by omega) with rfl|rfl|rfl|rfl
          · exact ok218
          · exact ok219
          · exact ok220
          · exact ok221
  ·
    by_cases h237 : a < 237
    ·
      by_cases h229 : a < 229
      ·
        by_cases h225 : a < 225
        ·
          rcases (show a=222 ∨ a=223 ∨ a=224 by omega) with rfl|rfl|rfl
          · exact ok222
          · exact ok223
          · exact ok224
        ·
          rcases (show a=225 ∨ a=226 ∨ a=227 ∨ a=228 by omega) with rfl|rfl|rfl|rfl
          · exact ok225
          · exact ok226
          · exact ok227
          · exact ok228
      ·
        by_cases h233 : a < 233
        ·
          rcases (show a=229 ∨ a=230 ∨ a=231 ∨ a=232 by omega) with rfl|rfl|rfl|rfl
          · exact ok229
          · exact ok230
          · exact ok231
          · exact ok232
        ·
          rcases (show a=233 ∨ a=234 ∨ a=235 ∨ a=236 by omega) with rfl|rfl|rfl|rfl
          · exact ok233
          · exact ok234
          · exact ok235
          · exact ok236
    ·
      by_cases h244 : a < 244
      ·
        by_cases h240 : a < 240
        ·
          rcases (show a=237 ∨ a=238 ∨ a=239 by omega) with rfl|rfl|rfl
          · exact ok237
          · exact ok238
          · exact ok239
        ·
          rcases (show a=240 ∨ a=241 ∨ a=242 ∨ a=243 by omega) with rfl|rfl|rfl|rfl
          · exact ok240
          · exact ok241
          · exact ok242
          · exact ok243
      ·
        by_cases h248 : a < 248
        ·
          rcases (show a=244 ∨ a=245 ∨ a=246 ∨ a=247 by omega) with rfl|rfl|rfl|rfl
          · exact ok244
          · exact ok245
          · exact ok246
          · exact ok247
        ·
          rcases (show a=248 ∨ a=249 ∨ a=250 ∨ a=251 by omega) with rfl|rfl|rfl|rfl
          · exact ok248
          · exact ok249
          · exact ok250
          · exact ok251
